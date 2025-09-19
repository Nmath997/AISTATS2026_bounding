#──────────────────────── 0. ライブラリ ────────────────────────#
# install.packages(c("Matrix","Rglpk","dplyr","tidyr","e1071","purrr","tibble"))
library(Matrix)
library(Rglpk)
library(dplyr)
library(tidyr)
library(e1071)
library(purrr)
library(tibble)

#──────────────────────── 0.1 グローバル方針・トレランス ──────────#
# ※「理論値」の安全装置：クリップや再正規化は“しない”。
#   ただし浮動小数の微小負や総和ズレを検出し、閾値超過なら NA を返す。
THEORY_NEG_TOL <- 1e-10  # 負の値の絶対値がこれを超えたら NA
THEORY_SUM_TOL <- 1e-8   # 合計1からのズレがこれを超えたら NA

# 目標：ここに新旧すべての結果を追加していく（★名称変更）
#───────────────────[ANCHOR A: RESULT オブジェクト定義]───────────────────#
`0913revised_RESULT_identification_examination_another` <- list()
RESULT_ident_0913revised_another <- `0913revised_RESULT_identification_examination_another`

#──────────────────────── 1. 基本パラメータ ──────────────────#
m <- 3                       # 潜在反応変数の本数 (Y1..Ym)
n <- 3                       # 各 Y の水準数
N_default <- 100             # デフォルトの標本サイズ（下の実行部で上書き可）
M_default <- 100             # デフォルトの必要レプリケート数（下の実行部で上書き可）

#──────────────────────── 2. グリッド生成 ───────────────────#
Y_list <- setNames(lapply(seq_len(m), \(.) seq_len(n)),
                   paste0("Y", seq_len(m)))
grid <- do.call(expand.grid,
                c(Y_list,
                  list(X = seq_len(m)),
                  list(Y = seq_len(n))))
Z <- nrow(grid)              # 変数 (確率質点) の数

# ケース名（順序固定）
CASE_LEVELS <- c("exp", "obs", "both", "exp_true", "obs_true", "both_true")

#──────────────────────── 3. ユーティリティ関数 ──────────────#
monotone_idx <- function(grid, m){
  ok <- rep(TRUE, nrow(grid))
  for(i in seq_len(m-1)){
    ok <- ok & (grid[[paste0("Y",i)]] <= grid[[paste0("Y",i+1)]])
  }
  which(ok)
}
consistency_bad <- function(grid, m){
  Y_cols <- paste0("Y", seq_len(m))
  Y_mat  <- as.matrix(grid[, Y_cols])
  picked <- Y_mat[cbind(seq_len(nrow(grid)), as.integer(grid$X))]
  which(picked != grid$Y)
}
relation_idx <- function(grid, i, j, rel){
  Yi <- grid[[paste0("Y", i)]]
  Yj <- grid[[paste0("Y", j)]]
  switch(rel,
         "<"  = which(Yi <  Yj),
         "<=" = which(Yi <= Yj),
         "="  = which(Yi == Yj),
         ">=" = which(Yi >= Yj),
         ">"  = which(Yi >  Yj),
         integer(0))
}

# ── 関係ブロック（Z はローカル推奨） ──
relation_blocks <- function(rel_mat, lb, ub, grid) {
  idx_all <- seq_len(nrow(grid))
  for(i in seq_len(nrow(rel_mat))) {
    for(j in seq_len(ncol(rel_mat))) {
      rel <- rel_mat[i, j]
      if(is.na(rel)) next
      idx_all <- intersect(idx_all, relation_idx(grid, i, j, rel))
    }
  }
  if(length(idx_all)==0) return(list())
  Zloc <- nrow(grid)
  row <- integer(Zloc); row[idx_all] <- 1
  blocks <- list()
  if(!is.null(lb)) blocks[["lb_event"]] <- list(mat = Matrix(row, 1), dir = ">=", rhs = lb)
  if(!is.null(ub)) blocks[["ub_event"]] <- list(mat = Matrix(row, 1), dir = "<=", rhs = ub)
  blocks
}
compile_blocks <- function(blocks){
  mats <- lapply(blocks, `[[`, "mat")
  keep <- !sapply(mats, is.null)
  A   <- do.call(rbind,  mats[keep])
  dir <- unlist(lapply(blocks[keep], `[[`, "dir"))
  rhs <- unlist(lapply(blocks[keep], `[[`, "rhs"))
  list(A=A, dir=dir, rhs=rhs)
}
marginal_mat <- function(idx_list, Z){
  rows <- rep(seq_along(idx_list), lengths(idx_list))
  cols <- unlist(idx_list)
  sparseMatrix(i = rows, j = cols, x = 1, dims = c(length(idx_list), Z))
}

# 任意ペア (i,j) の帯域単調 0<=Yi-Yj<=k のインデックス
band_idx_pair <- function(grid, i, j, k) {
  Yi <- grid[[paste0("Y", i)]]
  Yj <- grid[[paste0("Y", j)]]
  which((Yi - Yj) >= 0 & (Yi - Yj) <= k)
}
# 全ペア同時 0<=Yi-Yj<=k
band_idx <- function(grid, m, k) {
  ok <- rep(TRUE, nrow(grid))
  for (i in seq_len(m)) for (j in seq_len(i-1)) {
    Yi <- grid[[paste0("Y", i)]]
    Yj <- grid[[paste0("Y", j)]]
    ok <- ok & (Yi - Yj >= 0) & (Yi - Yj <= k)
    if (!any(ok)) return(integer(0))
  }
  which(ok)
}
event_blocks_from_idx <- function(idx, lb = NULL, ub = NULL, grid) {
  if (is.null(idx)) return(list())
  if (is.list(idx)) idx <- unlist(idx, recursive = TRUE, use.names = FALSE)
  idx <- as.integer(idx)
  idx <- idx[is.finite(idx) & !is.na(idx)]
  Zloc <- nrow(grid)
  idx <- idx[idx >= 1 & idx <= Zloc]
  if (length(idx) == 0) return(list())
  row <- integer(Zloc); row[idx] <- 1
  out <- list()
  if (!is.null(lb)) out[["lb_event"]] <- list(mat = Matrix(row,1), dir = ">=", rhs = lb)
  if (!is.null(ub)) out[["ub_event"]] <- list(mat = Matrix(row,1), dir = "<=", rhs = ub)
  out
}

#──────────────────────── 4. 目的関数指定 ──────────────────#
make_obj <- function(obj_spec, grid){
  Z <- nrow(grid); v <- rep(TRUE, Z)
  apply_conditions <- function(v, grid, conds){
    for(cond in conds){
      Yi <- grid[[paste0("Y", cond$var)]]
      v  <- v & switch(cond$op,
                       "==" = Yi == cond$val,
                       "<"  = Yi  < cond$val,
                       "<=" = Yi <= cond$val,
                       ">"  = Yi  > cond$val,
                       ">=" = Yi >= cond$val,
                       stop("unsupported op: ", cond$op))
    }
    v
  }
  if (obj_spec$type == "conditional") {
    if (!is.null(obj_spec$target_eq)) {
      eq_idx <- which(!is.na(obj_spec$target_eq))
      eq_list <- lapply(eq_idx, function(i){list(var=i, op="==", val=obj_spec$target_eq[i])})
      v <- apply_conditions(v, grid, eq_list)
    }
    if (!is.null(obj_spec$target_ineq)) v <- apply_conditions(v, grid, obj_spec$target_ineq)
    if (!is.null(obj_spec$condX)) v <- v & (grid$X == obj_spec$condX)
    if (!is.null(obj_spec$condY)) v <- v & (grid$Y == obj_spec$condY)
    obj_vec <- as.integer(v)
    denom_lab <- NULL
    if (!is.null(obj_spec$condX) && !is.null(obj_spec$condY)) {
      denom_lab <- sprintf("obs_k%d_y%d", obj_spec$condX, obj_spec$condY)
    } else if (!is.null(obj_spec$condX)) {
      denom_lab <- sprintf("obs_k%d_yALL", obj_spec$condX)
    } else if (!is.null(obj_spec$condY)) {
      denom_lab <- sprintf("obs_kALL_y%d", obj_spec$condY)
    }
    labels <- character()
    if (!is.null(obj_spec$target_eq)) {
      eq_idx <- which(!is.na(obj_spec$target_eq))
      labels <- c(labels, paste0("Y", eq_idx, "=", obj_spec$target_eq[eq_idx]))
    }
    if (!is.null(obj_spec$target_ineq)) {
      labels <- c(labels, vapply(obj_spec$target_ineq,
                                 function(c) paste0("Y",c$var,c$op,c$val), ""))
    }
    target_label <- if(length(labels)>0) paste(labels, collapse=",") else "ALL"
    cond_parts <- character()
    if (!is.null(obj_spec$condX)) cond_parts <- c(cond_parts, sprintf("X=%d", obj_spec$condX))
    if (!is.null(obj_spec$condY)) cond_parts <- c(cond_parts, sprintf("Y=%d", obj_spec$condY))
    cond_label <- if(length(cond_parts)>0) paste0("|", paste(cond_parts, collapse=",")) else ""
    obj_label <- sprintf("P(%s%s)", target_label, cond_label)
    return(list(obj_vec=obj_vec, denom_lab=denom_lab, obj_label=obj_label))
  } else if (obj_spec$type == "joint") {
    if (!is.null(obj_spec$target_eq)) {
      eq_idx <- which(!is.na(obj_spec$target_eq))
      eq_list <- lapply(eq_idx, function(i){list(var=i, op="==", val=obj_spec$target_eq[i])})
      v <- apply_conditions(v, grid, eq_list)
    }
    if (!is.null(obj_spec$target_ineq)) v <- apply_conditions(v, grid, obj_spec$target_ineq)
    if (!is.null(obj_spec$condX)) v <- v & (grid$X == obj_spec$condX)
    if (!is.null(obj_spec$condY)) v <- v & (grid$Y == obj_spec$condY)
    obj_vec <- as.integer(v)
    labels <- character()
    if (!is.null(obj_spec$target_eq)) {
      eq_idx <- which(!is.na(obj_spec$target_eq))
      labels <- c(labels, paste0("Y", eq_idx, "=", obj_spec$target_eq[eq_idx]))
    }
    if (!is.null(obj_spec$target_ineq)) {
      labels <- c(labels, vapply(obj_spec$target_ineq,
                                 function(c) paste0("Y",c$var,c$op,c$val), ""))
    }
    base_label <- if(length(labels)>0) paste(labels, collapse=",") else "Y1…Ym"
    cond_label <- if(!is.null(obj_spec$condX) && !is.null(obj_spec$condY))
      sprintf("|X=%d,Y=%d", obj_spec$condX, obj_spec$condY) else ""
    obj_label <- sprintf("P(%s%s)", base_label, cond_label)
    return(list(obj_vec=obj_vec, denom_lab=NULL, obj_label=obj_label))
  } else if (obj_spec$type == "order") {
    rel_mat <- obj_spec$rel_mat
    idx <- seq_len(Z)
    for (i in seq_len(nrow(rel_mat))) for (j in seq_len(ncol(rel_mat))) {
      rel <- rel_mat[i, j]
      if (!is.na(rel)) idx <- intersect(idx, relation_idx(grid, i, j, rel))
    }
    obj_vec <- integer(Z); obj_vec[idx] <- 1
    terms <- which(!is.na(rel_mat), arr.ind=TRUE)
    label_terms <- apply(terms, 1, function(rc) paste0("Y", rc[1], rel_mat[rc[1], rc[2]], "Y", rc[2]))
    obj_label <- paste0("P(", paste(label_terms, collapse=" & "), ")")
    list(obj_vec=obj_vec, denom_lab=NULL, obj_label=obj_label)
  } else if (obj_spec$type == "linear") {
    Zloc <- nrow(grid)
    cond_mask <- rep(TRUE, Zloc)
    if (!is.null(obj_spec$condX)) cond_mask <- cond_mask & (grid$X == obj_spec$condX)
    if (!is.null(obj_spec$condY)) cond_mask <- cond_mask & (grid$Y == obj_spec$condY)
    if (!is.null(obj_spec$w_vec)) {
      stopifnot(length(obj_spec$w_vec) == Zloc)
      w <- as.numeric(obj_spec$w_vec)
    } else {
      stopifnot(length(obj_spec$var_coefs) == m)
      intercept <- if (!is.null(obj_spec$intercept)) as.numeric(obj_spec$intercept) else 0
      zero_based <- isTRUE(obj_spec$zero_based)
      y_mat <- sapply(seq_len(m), function(k) {
        vals <- as.numeric(grid[[paste0("Y", k)]])
        if (zero_based) vals <- vals - 1
        vals
      })
      w <- rep(intercept, Zloc) + as.numeric(y_mat %*% as.numeric(obj_spec$var_coefs))
    }
    w_num <- w; w_num[!cond_mask] <- 0
    denom_lab <- NULL
    if (!is.null(obj_spec$condX) && !is.null(obj_spec$condY)) {
      denom_lab <- sprintf("obs_k%d_y%d", obj_spec$condX, obj_spec$condY)
    } else if (!is.null(obj_spec$condX)) {
      denom_lab <- sprintf("obs_k%d_yALL", obj_spec$condX)
    } else if (!is.null(obj_spec$condY)) {
      denom_lab <- sprintf("obs_kALL_y%d", obj_spec$condY)
    }
    label_cond <- ""
    if (!is.null(obj_spec$condX) || !is.null(obj_spec$condY)) {
      parts <- c()
      if (!is.null(obj_spec$condX)) parts <- c(parts, sprintf("X=%d", obj_spec$condX - 1))
      if (!is.null(obj_spec$condY)) parts <- c(parts, sprintf("Y=%d", obj_spec$condY - 1))
      label_cond <- paste0("|", paste(parts, collapse=","))
    }
    obj_label <- if (!is.null(obj_spec$label_override)) obj_spec$label_override else paste0("E[g(Y)", label_cond, "]")
    return(list(obj_vec = w_num, denom_lab = denom_lab, obj_label = obj_label))
  } else stop("unknown type")
}

#──────────────────────── 4.1 目的関数セット（★指定通り） ──────────#
#───────────────────[ANCHOR B: obj_specs 定義]───────────────────#
obj_specs <- list(
  "P(Y0=0,Y1=0,Y2=1)" = list(type="joint", target_eq=c(1,1,2), condX=NULL, condY=NULL),
  #"P(Y0=1,Y1=1,Y2=1)" = list(type="joint", target_eq=c(2,2,2), condX=NULL, condY=NULL),
  #"P(Y0=1,Y1=2,Y2=2)" = list(type="joint", target_eq=c(2,3,3), condX=NULL, condY=NULL),
  #"P(Y0=2,Y1=2,Y2=2)" = list(type="joint", target_eq=c(3,3,3), condX=NULL, condY=NULL),
  #"P(Y0=0,Y1=1,Y2=2)" = list(type="joint", target_eq=c(1,2,3), condX=NULL, condY=NULL)#,
  "E[Y1-Y0|X=2,Y=2]"  = list(
    type="linear",
    var_coefs=c(-1,1,0), intercept=0, zero_based=TRUE,
    condX=3, condY=3, label_override="E[Y1-Y0|X=2,Y=2]"
  )
)

#──────────────────────── 5. シナリオ定義 ───────────────────#
bad_rows <- consistency_bad(grid, m)
zero_mat <- function(idx, Z){
  if(length(idx)==0) return(NULL)
  sparseMatrix(i = seq_along(idx), j = idx, x = 1, dims = c(length(idx), Z))
}
base_blocks <- list(
  sum = list(mat = Matrix(1,1,Z,sparse=TRUE), dir = "==", rhs = 1),
  zero = list(mat = zero_mat(bad_rows, Z), dir = rep("==", length(bad_rows)), rhs = rep(0, length(bad_rows)))
)
constraint_scenarios <- list(
  "(I)" = list(                       # (viii-a): 0<=Ys-Yt<=1 a.s.
    apply_to = c("exp","obs","both"),
    band_k   = 1,
    exogeneity = FALSE
  ),
  "(II)" = list(                      # (viii-b): 0<=Ys-Yt<=1 a.s. + exogeneity (obs/both のみ)
    apply_to = c("obs"),
    band_k   = 1,
    exogeneity = TRUE
  )
)

#──────────────────────── 6. PO分布の構築（真値：そのまま） ──────────#
a_xy <- matrix(c(
  1/7,  1/7,  1/21,
  2/21, 1/7,  2/21,
  1/21, 1/7,  1/7
), nrow = m, ncol = n, byrow = TRUE)
a_xy <- a_xy / sum(a_xy)

k_true  <- 1
good_idx <- setdiff(band_idx(grid, m, k_true), consistency_bad(grid, m))
denom_xy <- table(
  factor(grid$X[good_idx], levels = seq_len(m)),
  factor(grid$Y[good_idx], levels = seq_len(n))
)
denom_xy <- as.matrix(denom_xy)
if (any(denom_xy == 0)) {
  stop("Some (x,y) cells have zero admissible configs under monotonicity+consistency.")
}
po_prob <- numeric(Z)
ix <- good_idx
po_prob[ix] <- a_xy[cbind(grid$X[ix], grid$Y[ix])] / denom_xy[cbind(grid$X[ix], grid$Y[ix])]
stopifnot(abs(sum(po_prob) - 1) < 1e-12)

# 便利：真の周辺（検証用）
pxy_mat_true <- tapply(po_prob, list(grid$X, grid$Y), sum)
pXY_true     <- as.vector(t(pxy_mat_true))
pY_list_true <- lapply(seq_len(m), function(k) as.numeric(tapply(po_prob, grid[[paste0("Y", k)]], sum)))

#──────────────────────── 7. LP ラッパ ───────────────────────#
run_lp_safe <- function(obj, A, dir, rhs, maximise = FALSE) {
  ctrl1 <- list(canonicalize_status=TRUE, presolve=TRUE,  verbose=FALSE, tm_limit=0)
  ctrl2 <- list(canonicalize_status=TRUE, presolve=FALSE, verbose=FALSE, tm_limit=0)
  bounds <- list(
    lower = list(ind = seq_len(length(obj)), val = rep(0, length(obj))),
    upper = list(ind = seq_len(length(obj)), val = rep(1, length(obj)))
  )
  .solve <- function(ctrl) Rglpk::Rglpk_solve_LP(
    obj=obj, mat=A, dir=dir, rhs=rhs, bounds=bounds, max=maximise, control=ctrl
  )
  sol <- .solve(ctrl1)
  if (!is.null(sol$status) && sol$status == 0) return(sol)
  sol2 <- .solve(ctrl2)
  if (!is.null(sol2$status) && sol2$status == 0) return(sol2)
  sol2
}


# ===== ADD: 理論値が“strict”で安全に計算できるか（全目的関数で判定） =====
theory_ok_for_all_objs <- function(obj_specs, grid, pXY, pY_list, m, n) {
  for (nm in names(obj_specs)) {
    spec <- obj_specs[[nm]]
    
    # Theorem 4（観測+外生性）: すべての目的関数で要求
    v4 <- eval_theorem4_for_obj(spec, grid, pXY, m, n)  # strict 安全装置つき
    if (is.na(v4)) return(FALSE)
    
    # Theorem 3（実験のみ）: condX/condY が無い目的にのみ要求（線形の条件付は対象外）
    apply_I <- is.null(spec$condX) && is.null(spec$condY)
    if (apply_I) {
      v3 <- eval_theorem3_for_obj(spec, grid, pY_list, m, n)  # strict 安全装置つき
      if (is.na(v3)) return(FALSE)
    }
  }
  TRUE
}




#──────────────────────── 7.5 可否判定・サンプル収集（新規） ─────────#
# marginals 用の行列（名前付き）
.build_marginal_mats <- function(grid, m, n) {
  Z <- nrow(grid)
  idx_exp <- idx_obs <- vector("list", m*n)
  cnt <- 1
  for(k in seq_len(m)) for(y in seq_len(n)){
    idx_exp[[cnt]] <- which(grid[[paste0("Y",k)]] == y)
    idx_obs[[cnt]] <- which(grid$X==k & grid$Y==y)
    cnt <- cnt + 1
  }
  names(idx_exp) <- sprintf("exp_k%d_y%d", rep(seq_len(m), each=n), rep(seq_len(n), m))
  names(idx_obs) <- sprintf("obs_k%d_y%d", rep(seq_len(m), each=n), rep(seq_len(n), m))
  list(mat_exp = marginal_mat(idx_exp, Z),
       mat_obs = marginal_mat(idx_obs, Z),
       nms_exp = names(idx_exp),
       nms_obs = names(idx_obs))
}

# サンプル可否（全シナリオの適用ケースで可行解があるか）
is_feasible_sample <- function(pXY_vec, pY_list, grid, m, n, marginals_cache = NULL) {
  if (is.null(marginals_cache)) marginals_cache <- .build_marginal_mats(grid, m, n)
  Zloc <- nrow(grid)
  dummy_obj <- rep(0, Zloc)  # 目的関数非依存で可否だけ確認
  # 右辺ベクトル（名前付き）
  b_obs <- pXY_vec; names(b_obs) <- marginals_cache$nms_obs
  b_exp <- unlist(pY_list); names(b_exp) <- marginals_cache$nms_exp
  # pX（外生性用）
  get_pX_from_vec <- function(pXY_vec, m, n) tapply(pXY_vec, rep(seq_len(m), each=n), sum)
  pX <- get_pX_from_vec(pXY_vec, m, n)
  for (sname in names(constraint_scenarios)) {
    sc <- constraint_scenarios[[sname]]
    # 関係ブロック
    rel_blks <- list()
    if (!is.null(sc$band_k)) {
      idx_band <- band_idx(grid, m, sc$band_k)
      rel_blks <- c(rel_blks, event_blocks_from_idx(idx_band, lb=1, ub=NULL, grid))
    }
    if (isTRUE(sc$exogeneity)) {
      stopifnot(length(pX)==m, abs(sum(pX)-1)<1e-8)
      Z <- nrow(grid); Ycols <- paste0("Y", seq_len(m))
      Y_mat <- as.matrix(grid[, Ycols])
      cons_row <- (Y_mat[cbind(seq_len(Z), as.integer(grid$X))] == grid$Y)
      make_row <- function(i, r, x) {
        idx_irx  <- which(grid[[Ycols[i]]] == r & grid$X == x & cons_row)
        idx_ir   <- which(grid[[Ycols[i]]] == r & cons_row)
        v <- numeric(Z)
        if (length(idx_irx)) v[idx_irx] <- v[idx_irx] + 1
        if (length(idx_ir))  v[idx_ir]  <- v[idx_ir]  - pX[x]
        v
      }
      rows <- list()
      for (i in seq_len(m)) for (r in seq_len(n)) for (x in seq_len(m)) rows[[length(rows)+1]] <- make_row(i, r, x)
      Aexo <- Matrix(do.call(rbind, rows), sparse = TRUE)
      rel_blks <- c(rel_blks, list(exog = list(mat=Aexo, dir=rep("==", nrow(Aexo)), rhs=rep(0, nrow(Aexo)))))
    }
    apply_to <- if (is.null(sc$apply_to)) c("exp","obs","both") else sc$apply_to
    for (cname in apply_to) {
      add <- switch(cname,
                    exp  = list(mat=marginals_cache$mat_exp, dir=rep("==",nrow(marginals_cache$mat_exp)), rhs=b_exp),
                    obs  = list(mat=marginals_cache$mat_obs, dir=rep("==",nrow(marginals_cache$mat_obs)), rhs=b_obs),
                    both = list(mat=rbind(marginals_cache$mat_exp, marginals_cache$mat_obs),
                                dir=rep("==", nrow(marginals_cache$mat_exp)+nrow(marginals_cache$mat_obs)),
                                rhs=c(b_exp,b_obs)))
      cmp <- compile_blocks(c(base_blocks, rel_blks, list(marg=add)))
      sol <- run_lp_safe(dummy_obj, cmp$A, cmp$dir, cmp$rhs, FALSE)
      if (is.null(sol$status) || sol$status != 0) return(FALSE)
    }
  }
  TRUE
}

# 指定 N で可行なレプリケート M 個を収集（Yi と (X,Y) は同一サンプルから周辺化）
# ===== REPLACE: collect_feasible_samples =====
# ===== REPLACE: collect_feasible_samples (2N_split 版) =====
collect_feasible_samples <- function(N, M, grid, po_prob, m, n,
                                     obj_specs,
                                     require_theory_safe = FALSE,
                                     max_draws = 100000) {
  # N は「Exp に使う N == Obs に使う N」とする（2N_split で 2N ドロー）
  marginals_cache <- .build_marginal_mats(grid, m, n)
  samples <- vector("list", M)
  got <- 0; draws <- 0
  Zloc <- nrow(grid)
  while (got < M) {
    draws <- draws + 1
    if (draws > max_draws) {
      stop(sprintf("可行サンプル（2N_split）が十分に集まりません（theory_filter=%s, N=%d, 要=%d, 試行=%d）",
                   as.character(require_theory_safe), N, M, draws))
    }
    # ---- 2N_split ----
    idx_all <- sample.int(Zloc, size = 2L*N, replace = TRUE, prob = po_prob)
    idx_exp <- idx_all[1:N]          # 前半 N → 実験周辺
    idx_obs <- idx_all[(N+1):(2*N)]  # 後半 N → 観測周辺
    
    # 実験周辺 P(Yk) を Exp 部分から
    pY_list_hat <- lapply(seq_len(m), function(k) {
      yk <- grid[[paste0("Y",k)]][idx_exp]
      as.numeric(tabulate(yk, nbins = n)) / N
    })
    # 観測周辺 P(X,Y) を Obs 部分から
    tab_xy <- table(factor(grid$X[idx_obs], levels = seq_len(m)),
                    factor(grid$Y[idx_obs], levels = seq_len(n)))
    pXY_hat <- as.vector(t(tab_xy)) / N  # N_obs=N
    
    # ---- 可否チェック ----
    ok_lp <- is_feasible_sample(pXY_hat, pY_list_hat, grid, m, n, marginals_cache)
    
    ok_th <- TRUE
    if (require_theory_safe) {
      ok_th <- theory_ok_for_all_objs(obj_specs, grid, pXY_hat, pY_list_hat, m, n)
    }
    
    if (ok_lp && ok_th) {
      got <- got + 1
      samples[[got]] <- list(pXY = pXY_hat, pY_list = pY_list_hat)
    }
  }
  samples
}



#──────────────────────── 8. 目的関数毎の LP/理論値評価 ───────────#
#（★グローバル変数に依存しない形へ修正）

# Theorem 3: 実験データのみで P(Ys) を識別（安全装置＝閾値超過なら NA）
theorem3_po_probs <- function(pY_list, m, n){
  if (!(length(pY_list)==m && all(sapply(pY_list, length)==n))) return(list(patterns=NULL, probs=rep(NA_real_, 1), ok=FALSE))
  cdf <- function(v) cumsum(v)
  CY <- lapply(pY_list, cdf)
  pats <- {
    pats <- list()
    for (y0 in 1:n) pats[[length(pats)+1]] <- list(type="A", y0=y0, vec=rep(y0, m))
    for (y0 in 1:(n-1)) for (k in 1:(m-1)) pats[[length(pats)+1]] <- list(type="B", y0=y0, k=k, vec=c(rep(y0, k), rep(y0+1, m-k)))
    pats
  }
  probs <- numeric(length(pats))
  for (i in seq_along(pats)) {
    pat <- pats[[i]]
    if (pat$type=="A") {
      y0r <- pat$y0
      s1 <- CY[[m]][y0r]
      s0 <- if (y0r>1) CY[[1]][y0r-1] else 0
      probs[i] <- s1 - s0
    } else {
      y0r <- pat$y0; k <- pat$k
      probs[i] <- CY[[k]][y0r] - CY[[k+1]][y0r]
    }
  }
  # 安全装置：強い負や総和ズレなら NG
  if (any(probs < -THEORY_NEG_TOL) || abs(sum(probs) - 1) > THEORY_SUM_TOL)
    return(list(patterns=pats, probs=rep(NA_real_, length(pats)), ok=FALSE))
  # 微小負は 0 に切上げ（再正規化はしない）
  probs[probs < 0 & probs > -THEORY_NEG_TOL] <- 0
  list(patterns = pats, probs = probs, ok=TRUE)
}

# Theorem 4: 観察+外生性で P(Ys,X,Y) を識別（安全装置＝閾値超過なら NA）
theorem4_grid_probs <- function(grid, pXY, m, n){
  if (length(pXY)!=m*n) return(rep(NA_real_, nrow(grid)))
  # P(X), P(Y|X)
  pX <- tapply(pXY, rep(seq_len(m), each=n), sum)
  pY_given_X <- matrix(0, nrow=m, ncol=n)
  for (x in 1:m) {
    if (pX[x] > 0) pY_given_X[x,] <- pXY[((x-1)*n+1):(x*n)] / pX[x]
  }
  CYX <- t(apply(pY_given_X, 1, cumsum))
  pats <- {
    pats <- list()
    for (y0 in 1:n) pats[[length(pats)+1]] <- list(type="A", y0=y0, vec=rep(y0, m))
    for (y0 in 1:(n-1)) for (k in 1:(m-1)) pats[[length(pats)+1]] <- list(type="B", y0=y0, k=k, vec=c(rep(y0, k), rep(y0+1, m-k)))
    pats
  }
  p <- numeric(nrow(grid))
  for (pp in pats) {
    if (pp$type=="A") {
      y0r <- pp$y0
      expr <- CYX[m, y0r] - if (y0r>1) CYX[1, y0r-1] else 0
      for (x in 1:m) {
        y <- y0r
        idx <- which(grid$X==x & grid$Y==y & Reduce("&", lapply(1:m, function(j) grid[[paste0("Y",j)]]==pp$vec[j])))
        if (length(idx)) p[idx] <- p[idx] + expr * pX[x]
      }
    } else {
      y0r <- pp$y0; k <- pp$k
      expr <- CYX[k, y0r] - CYX[k+1, y0r]
      if (k>=1) for (x in 1:k) {
        y <- y0r
        idx <- which(grid$X==x & grid$Y==y & Reduce("&", lapply(1:m, function(j) grid[[paste0("Y",j)]]==pp$vec[j])))
        if (length(idx)) p[idx] <- p[idx] + expr * pX[x]
      }
      if (k+1<=m) for (x in (k+1):m) {
        y <- y0r+1
        idx <- which(grid$X==x & grid$Y==y & Reduce("&", lapply(1:m, function(j) grid[[paste0("Y",j)]]==pp$vec[j])))
        if (length(idx)) p[idx] <- p[idx] + expr * pX[x]
      }
    }
  }
  # 安全装置
  if (any(p < -THEORY_NEG_TOL) || abs(sum(p)-1) > THEORY_SUM_TOL) return(rep(NA_real_, length(p)))
  p[p < 0 & p > -THEORY_NEG_TOL] <- 0
  p
}

# Theorem 3 に基づく目的関数値（可能なら）
eval_theorem3_for_obj <- function(obj_spec, grid, pY_list, m, n){
  pats <- theorem3_po_probs(pY_list, m, n)
  if (isFALSE(pats$ok) || all(is.na(pats$probs))) return(NA_real_)
  # X,Y 条件がある場合は適用外
  if (!is.null(obj_spec$condX) || !is.null(obj_spec$condY)) return(NA_real_)
  if (obj_spec$type=="joint" || obj_spec$type=="order") {
    pick <- logical(length(pats$patterns))
    for (i in seq_along(pats$patterns)) {
      yv <- pats$patterns[[i]]$vec
      ok <- TRUE
      if (!is.null(obj_spec$target_eq)) {
        eq_idx <- which(!is.na(obj_spec$target_eq))
        for (j in eq_idx) if (yv[j] != obj_spec$target_eq[j]) { ok <- FALSE; break }
      }
      if (ok && !is.null(obj_spec$target_ineq)) {
        for (cond in obj_spec$target_ineq) {
          val <- yv[cond$var]
          ok <- ok & switch(cond$op,
                            "==" = (val==cond$val),
                            "<"  = (val< cond$val),
                            "<=" = (val<=cond$val),
                            ">"  = (val> cond$val),
                            ">=" = (val>=cond$val))
          if (!ok) break
        }
      }
      pick[i] <- ok
    }
    return(sum(pats$probs[pick]))
  } else if (obj_spec$type=="linear") {
    # 無条件の E[g(Ys)] のみ対応（本セットには含まれないが残しておく）
    if (!is.null(obj_spec$w_vec)) stop("theorem3: linear with w_vec not supported.")
    stopifnot(length(obj_spec$var_coefs)==m)
    intercept <- if (!is.null(obj_spec$intercept)) as.numeric(obj_spec$intercept) else 0
    zero_based <- isTRUE(obj_spec$zero_based)
    g_of <- function(yv){
      vals <- yv; if (zero_based) vals <- vals - 1
      as.numeric(intercept + sum(obj_spec$var_coefs * vals))
    }
    val <- 0
    for (i in seq_along(pats$patterns)) val <- val + g_of(pats$patterns[[i]]$vec) * pats$probs[i]
    return(val)
  }
  NA_real_
}

# Theorem 4 に基づく目的関数値（可能なら）
eval_theorem4_for_obj <- function(obj_spec, grid, pXY, m, n){
  pgrid <- theorem4_grid_probs(grid, pXY, m, n)
  if (all(is.na(pgrid))) return(NA_real_)
  obj <- make_obj(obj_spec, grid)
  num <- sum(obj$obj_vec * pgrid)
  denom <- 1
  if (!is.null(obj$denom_lab)) {
    if (grepl("^obs_k\\d+_y\\d+$", obj$denom_lab)) {
      kk <- as.integer(sub("^obs_k(\\d+)_y(\\d+)$", "\\1", obj$denom_lab))
      yy <- as.integer(sub("^obs_k(\\d+)_y(\\d+)$", "\\2", obj$denom_lab))
      denom <- pXY[(kk-1)*n + yy]
    } else if (grepl("^obs_k\\d+_yALL$", obj$denom_lab)) {
      kk <- as.integer(sub("^obs_k(\\d+)_yALL$", "\\1", obj$denom_lab))
      denom <- sum(pXY[((kk-1)*n+1):(kk*n)])
    } else if (grepl("^obs_kALL_y\\d+$", obj$denom_lab)) {
      yy <- as.integer(sub("^obs_kALL_y(\\d+)$", "\\1", obj$denom_lab))
      denom <- sum(pXY[seq(yy, m*n, by=n)])
    } else denom <- NA_real_
  }
  if (!is.null(obj$denom_lab) && (is.na(denom) || denom<=0)) return(NA_real_)
  if (!is.null(obj$denom_lab)) return(num/denom) else return(num)
}

#──────────────────────── 8.1 run_for_obj（★引数化・非グローバル化） ─────#
#───────────────────[ANCHOR C: run_for_obj 定義]───────────────────#
run_for_obj <- function(obj_spec, spec_name, pXY_in, pY_list_in, rep_id = NULL){
  Z <- nrow(grid)
  # marginals 行列＆名前
  marginals_cache <- .build_marginal_mats(grid, m, n)
  has_exp <- is.list(pY_list_in) && length(pY_list_in)==m && all(sapply(pY_list_in, length)==n)
  has_obs <- is.numeric(pXY_in)  && length(pXY_in)==m*n
  cases <- character()
  if (has_exp)            cases <- c(cases, "exp")
  if (has_obs)            cases <- c(cases, "obs")
  if (has_exp && has_obs) cases <- c(cases, "both")
  if (length(cases)==0) stop("pY_list_in/pXY_in が未定義のため case を構成できません。")
  
  # 右辺ベクトル
  if (has_exp) { b_exp <- unlist(pY_list_in); names(b_exp) <- marginals_cache$nms_exp }
  if (has_obs) { b_obs <- pXY_in;              names(b_obs) <- marginals_cache$nms_obs }
  
  # pX（外生性用）
  get_pX_from_vec <- function(pXY_vec, m, n) tapply(pXY_vec, rep(seq_len(m), each=n), sum)
  pX <- if (has_obs) get_pX_from_vec(pXY_in, m, n) else NULL
  
  result_tbl <- data.frame(
    scenario   = character(),
    case       = character(),
    feasible   = logical(),
    min_val    = numeric(),
    max_val    = numeric(),
    min_status = integer(),
    max_status = integer(),
    rep        = integer(),
    stringsAsFactors = FALSE
  )
  
  for (sname in names(constraint_scenarios)) {
    sc <- constraint_scenarios[[sname]]
    # 関係ブロック
    rel_blks <- list()
    if (!is.null(sc$band_k)) {
      idx_band <- band_idx(grid, m, sc$band_k)
      rel_blks <- c(rel_blks, event_blocks_from_idx(idx_band, lb=1, ub=NULL, grid))
    }
    if (isTRUE(sc$exogeneity)) {
      if (is.null(pX)) stop(sprintf("exogeneity=TRUE ですが pX 未定義（scenario=%s）。", sname))
      Zloc <- nrow(grid); Ycols <- paste0("Y", seq_len(m))
      Y_mat <- as.matrix(grid[, Ycols])
      cons_row <- (Y_mat[cbind(seq_len(Zloc), as.integer(grid$X))] == grid$Y)
      make_row <- function(i, r, x) {
        idx_irx  <- which(grid[[Ycols[i]]] == r & grid$X == x & cons_row)
        idx_ir   <- which(grid[[Ycols[i]]] == r & cons_row)
        v <- numeric(Zloc)
        if (length(idx_irx)) v[idx_irx] <- v[idx_irx] + 1
        if (length(idx_ir))  v[idx_ir]  <- v[idx_ir]  - pX[x]
        v
      }
      rows <- list()
      for (i in seq_len(m)) for (r in seq_len(n)) for (x in seq_len(m)) rows[[length(rows) + 1]] <- make_row(i, r, x)
      Aexo <- Matrix(do.call(rbind, rows), sparse = TRUE)
      rel_blks <- c(rel_blks, list(exog = list(mat = Aexo, dir = rep("==", nrow(Aexo)), rhs = rep(0, nrow(Aexo)))))
    }
    apply_to <- if (is.null(sc$apply_to)) c("exp","obs","both") else sc$apply_to
    for (cname in cases) {
      if (!(cname %in% apply_to)) {
        # 不適用ケースは NA で占位（rep は付けない）
        result_tbl <- rbind(result_tbl, data.frame(
          scenario=sname, case=cname, feasible=FALSE,
          min_val=NA_real_, max_val=NA_real_, min_status=NA_integer_, max_status=NA_integer_,
          rep=if (is.null(rep_id)) NA_integer_ else rep_id, stringsAsFactors = FALSE))
        next
      }
      add <- switch(cname,
                    exp  = list(mat=marginals_cache$mat_exp, dir=rep("==", nrow(marginals_cache$mat_exp)), rhs=b_exp),
                    obs  = list(mat=marginals_cache$mat_obs, dir=rep("==", nrow(marginals_cache$mat_obs)), rhs=b_obs),
                    both = list(mat=rbind(marginals_cache$mat_exp, marginals_cache$mat_obs),
                                dir=rep("==", nrow(marginals_cache$mat_exp)+nrow(marginals_cache$mat_obs)),
                                rhs=c(b_exp,b_obs))
      )
      cmp <- compile_blocks(c(base_blocks, rel_blks, list(marg=add)))
      obj_vec <- make_obj(obj_spec, grid)$obj_vec
      sol_min <- run_lp_safe(obj_vec, cmp$A, cmp$dir, cmp$rhs, FALSE)
      sol_max <- run_lp_safe(obj_vec, cmp$A, cmp$dir, cmp$rhs, TRUE)
      feas <- (!is.null(sol_min$status) && sol_min$status==0 && !is.null(sol_max$status) && sol_max$status==0)
      # 分母処理（conditional/linear）
      obj <- make_obj(obj_spec, grid)
      denom <- 1
      if (!is.null(obj$denom_lab)) {
        if (exists("b_obs") && obj$denom_lab %in% names(b_obs)) {
          denom <- b_obs[obj$denom_lab]
        } else {
          if (grepl("^obs_k\\d+_yALL$", obj$denom_lab)) {
            k <- as.integer(sub("^obs_k(\\d+)_yALL$", "\\1", obj$denom_lab))
            denom <- sum(b_obs[sprintf("obs_k%d_y%d", k, 1:n)])
          } else if (grepl("^obs_kALL_y\\d+$", obj$denom_lab)) {
            yv <- as.integer(sub("^obs_kALL_y(\\d+)$", "\\1", obj$denom_lab))
            denom <- sum(b_obs[sprintf("obs_k%d_y%d", 1:m, yv)])
          } else denom <- NA_real_
        }
      }
      res_min <- if (!is.null(obj$denom_lab) && cname == "exp") NA_real_ else if (!is.null(obj$denom_lab) && (is.na(denom) || denom<=0)) NA_real_ else if (!is.null(obj$denom_lab)) sol_min$optimum/denom else sol_min$optimum
      res_max <- if (!is.null(obj$denom_lab) && cname == "exp") NA_real_ else if (!is.null(obj$denom_lab) && (is.na(denom) || denom<=0)) NA_real_ else if (!is.null(obj$denom_lab)) sol_max$optimum/denom else sol_max$optimum
      result_tbl <- rbind(result_tbl, data.frame(
        scenario=sname, case=cname, feasible=feas,
        min_val=res_min, max_val=res_max, min_status=sol_min$status, max_status=sol_max$status,
        rep=if (is.null(rep_id)) NA_integer_ else rep_id, stringsAsFactors = FALSE))
    }
  }
  
  # (LP)/(Theory) ラベル付けと理論値の付加
  # LP 側
  res_lp <- result_tbl %>%
    mutate(scenario = paste0(as.character(scenario), " (LP)")) %>%
    select(scenario, case, feasible, min_val, max_val, rep)
  
  # 理論値
  val_I  <- eval_theorem3_for_obj(obj_spec, grid, pY_list_in, m, n)
  val_II <- eval_theorem4_for_obj(obj_spec, grid, pXY_in,     m, n)
  
  theory_rows <- list()
  if (!is.na(val_I)) {
    for (cc in c("exp","obs","both")) {
      theory_rows[[length(theory_rows)+1]] <- data.frame(
        scenario="(I) (Theory)", case=cc, feasible=TRUE,
        min_val=val_I, max_val=val_I, rep=if (is.null(rep_id)) NA_integer_ else rep_id,
        stringsAsFactors = FALSE
      )
    }
  }
  if (!is.na(val_II)) {
    for (cc in c("obs","both")) {
      theory_rows[[length(theory_rows)+1]] <- data.frame(
        scenario="(II) (Theory)", case=cc, feasible=TRUE,
        min_val=val_II, max_val=val_II, rep=if (is.null(rep_id)) NA_integer_ else rep_id,
        stringsAsFactors = FALSE
      )
    }
  }
  res_theory <- if (length(theory_rows)) dplyr::bind_rows(theory_rows) else NULL
  res_all <- if (is.null(res_theory)) res_lp else dplyr::bind_rows(res_lp, res_theory)
  
  list(results = res_all, label = make_obj(obj_spec, grid)$obj_label)
}

#──────────────────────── 8.2 分割（既存のまま使用） ─────────────#
split_replicates <- function(rep_df) {
  preferred <- c("(I) (LP)", "(I) (Theory)", "(II) (LP)", "(II) (Theory)")
  scen_in_df <- unique(as.character(rep_df$scenario))
  scenario_levels <- c(preferred[preferred %in% scen_in_df], setdiff(scen_in_df, preferred))
  case_levels <- c("exp","obs","both")  # replicates には true 行を含めない前提
  
  rep_df <- rep_df |>
    dplyr::mutate(
      scenario = factor(as.character(scenario), levels = scenario_levels),
      case     = factor(as.character(case),     levels = case_levels)
    )
  
  by_scn <- split(rep_df, rep_df$scenario)
  by_scn <- by_scn[scenario_levels]
  
  lapply(by_scn, function(df_s) {
    by_case <- split(df_s, df_s$case)
    by_case <- by_case[case_levels]
    lapply(by_case, function(x) {
      if (nrow(x) == 0) return(as.data.frame(x))
      y <- x[, c("rep","min_val","max_val"), drop = FALSE]
      rownames(y) <- NULL
      as.data.frame(y)
    })
  })
}

#──────────────────────── 8.3 Nごとのシミュレーション（共通サンプル） ────#
simulate_for_N <- function(obj_specs, N, M, theory_filter = FALSE) {
  # 1) 可行レプリケート収集（Option C: theory_filter=TRUE なら理論OKまで抽出）
  samples <- collect_feasible_samples(
    N = N, M = M, grid = grid, po_prob = po_prob, m = m, n = n,
    obj_specs = obj_specs,
    require_theory_safe = theory_filter
  )
  
  # 2) 目的関数ごとに同じサンプルを適用
  out <- list()
  for (obj_name in names(obj_specs)) {
    rep_rows <- vector("list", M)
    for (r in seq_len(M)) {
      pXY_hat     <- samples[[r]]$pXY
      pY_list_hat <- samples[[r]]$pY_list
      res <- run_for_obj(
        obj_spec   = obj_specs[[obj_name]],
        spec_name  = obj_name,
        pXY_in     = pXY_hat,
        pY_list_in = pY_list_hat,
        rep_id     = r
      )
      rep_rows[[r]] <- res$results
    }
    
    # 3) レプリケート結合と並び順の整備
    rep_df <- dplyr::bind_rows(rep_rows)
    
    preferred <- c("(I) (LP)", "(I) (Theory)", "(II) (LP)", "(II) (Theory)")
    scen_in_df <- unique(as.character(rep_df$scenario))
    scenario_levels <- c(preferred[preferred %in% scen_in_df], setdiff(scen_in_df, preferred))
    
    rep_df <- rep_df |>
      dplyr::mutate(
        scenario = factor(as.character(scenario), levels = scenario_levels),
        case     = factor(as.character(case),     levels = c("exp","obs","both"))
      )
    
    # レプリケートのネスト（表出力向け）
    reps_nested <- split_replicates(rep_df)
    
    # 4) サマリー統計（LP/Theory 混在）
    safe_mean <- function(x) if (all(is.na(x))) NA_real_ else mean(x, na.rm = TRUE)
    safe_q    <- function(x, p) if (all(is.na(x))) NA_real_ else
      as.numeric(stats::quantile(x, probs = p, na.rm = TRUE, names = FALSE))
    
    summary_df <- rep_df |>
      dplyr::group_by(scenario, case) |>
      dplyr::summarise(
        n_rep         = dplyr::n(),
        n_feasible    = sum(feasible, na.rm = TRUE),
        feasible_rate = mean(feasible, na.rm = TRUE),
        mean_lb  = safe_mean(min_val),
        ci_lb_lo = safe_q(min_val, 0.025),
        ci_lb_hi = safe_q(min_val, 0.975),
        mean_ub  = safe_mean(max_val),
        ci_ub_lo = safe_q(max_val, 0.025),
        ci_ub_hi = safe_q(max_val, 0.975),
        .groups  = "drop"
      )
    
    # 5) 真の分布に対する LP（1回だけ）
    out_true_lp <- run_for_obj(
      obj_spec   = obj_specs[[obj_name]],
      spec_name  = obj_name,
      pXY_in     = pXY_true,
      pY_list_in = pY_list_true,
      rep_id     = NA_integer_
    )
    
    true_rows_lp <- out_true_lp$results |>
      dplyr::filter(grepl("\\(LP\\)$", scenario)) |>
      dplyr::mutate(
        case     = paste0(as.character(case), "_true"),
        mean_lb  = min_val,
        ci_lb_lo = min_val,
        ci_lb_hi = min_val,
        mean_ub  = max_val,
        ci_ub_lo = max_val,
        ci_ub_hi = max_val
      ) |>
      dplyr::select(scenario, case, mean_lb, ci_lb_lo, ci_lb_hi, mean_ub, ci_ub_lo, ci_ub_hi)
    
    # 6) 真の分布に対する Theory（Theorem 3/4 そのまま）
    val_I_true  <- eval_theorem3_for_obj(obj_specs[[obj_name]], grid, pY_list_true, m, n)
    val_II_true <- eval_theorem4_for_obj(obj_specs[[obj_name]], grid, pXY_true,     m, n)
    
    true_rows_th <- list()
    if (!is.na(val_I_true)) {
      for (cc in c("exp_true","obs_true","both_true")) {
        true_rows_th[[length(true_rows_th)+1]] <- data.frame(
          scenario = "(I) (Theory)",
          case     = cc,
          mean_lb  = val_I_true, ci_lb_lo = val_I_true, ci_lb_hi = val_I_true,
          mean_ub  = val_I_true, ci_ub_lo = val_I_true, ci_ub_hi = val_I_true,
          stringsAsFactors = FALSE
        )
      }
    }
    if (!is.na(val_II_true)) {
      for (cc in c("obs_true","both_true")) {
        true_rows_th[[length(true_rows_th)+1]] <- data.frame(
          scenario = "(II) (Theory)",
          case     = cc,
          mean_lb  = val_II_true, ci_lb_lo = val_II_true, ci_lb_hi = val_II_true,
          mean_ub  = val_II_true, ci_ub_lo = val_II_true, ci_ub_hi = val_II_true,
          stringsAsFactors = FALSE
        )
      }
    }
    true_rows_th <- if (length(true_rows_th)) dplyr::bind_rows(true_rows_th) else NULL
    
    # 7) サマリーへ真値（LP/Theory 両方）を結合
    summary_df <- dplyr::bind_rows(summary_df, true_rows_lp, true_rows_th) |>
      dplyr::mutate(
        scenario = factor(
          as.character(scenario),
          levels = c("(I) (LP)", "(I) (Theory)", "(II) (LP)", "(II) (Theory)")
        ),
        case     = factor(
          as.character(case),
          levels = c("exp","obs","both","exp_true","obs_true","both_true")
        )
      ) |>
      dplyr::arrange(scenario, case)
    
    out[[obj_name]] <- list(replicates = reps_nested, summary = as.data.frame(summary_df))
  }
  
  out
}


#──────────────────────── 9. 複数 N/M を回す・保存 ────────────────#
is_df_like <- function(x) inherits(x, c("data.frame", "tbl_df"))
is_atomic_like <- function(x) is.atomic(x) || is.matrix(x) || is_df_like(x)
deep_merge <- function(x, y) {
  if (!is.list(x) || is_atomic_like(x) || is_atomic_like(y)) return(y)
  for (nm in names(y)) x[[nm]] <- if (is.null(x[[nm]])) y[[nm]] else deep_merge(x[[nm]], y[[nm]])
  x
}

# ===== REPLACE: run_all =====
run_all <- function(obj_specs, N_values, M_values, theory_filter = FALSE) {
  out <- list()
  for (obj_name in names(obj_specs)) out[[obj_name]] <- list()
  for (Ncur in N_values) {
    N_key <- sprintf("N=%d", Ncur)
    for (Mcur in M_values) {
      M_key <- sprintf("M=%d", Mcur)
      res_all_objs <- simulate_for_N(obj_specs, N=Ncur, M=Mcur, theory_filter=theory_filter)
      for (obj_name in names(obj_specs)) {
        if (is.null(out[[obj_name]][[N_key]])) out[[obj_name]][[N_key]] <- list()
        out[[obj_name]][[N_key]][[M_key]] <- res_all_objs[[obj_name]]
      }
    }
  }
  out
}

# ===== REPLACE: add_runs =====
add_runs <- function(obj_specs, N_values, M_values, theory_filter = FALSE) {
  new_out <- run_all(obj_specs, N_values, M_values, theory_filter=theory_filter)
  if (!exists("0913revised_RESULT_identification_examination_another") ||
      !is.list(`0913revised_RESULT_identification_examination_another`)) {
    assign("0913revised_RESULT_identification_examination_another", new_out, envir = .GlobalEnv)
  } else {
    merged <- deep_merge(`0913revised_RESULT_identification_examination_another`, new_out)
    assign("0913revised_RESULT_identification_examination_another", merged, envir = .GlobalEnv)
  }
  cat(
    "Stored:", paste(names(new_out), collapse = ", "),
    "for N=", paste(N_values, collapse = ", "),
    "and", paste(sprintf("M=%d", M_values), collapse = ", "),
    sprintf("(theory_filter=%s)", as.character(theory_filter)),
    "\n"
  )
}

# ===== 実行セクション =====
#───────────────────[ANCHOR D: 実行セクション]───────────────────#
N_values <- c(10, 100, 1000, 10000)
M_values <- c(100)
add_runs(obj_specs, N_values, M_values, theory_filter = TRUE)
