#──────────────────────── 0. ライブラリ（最小限） ────────────────#
suppressPackageStartupMessages({
  library(Matrix)
  library(slam)      # GLPK に疎行列で渡す
  library(Rglpk)
  library(dplyr)     # 集計でのみ使用（出力互換のため）
})

#──────────────────────── 1. 基本パラメータ ──────────────────#
m <- 3     # 潜在反応変数本数 (Y1..Ym) = 3
n <- 3     # 各 Y の水準数
Z <- NULL  # 後で grid 作成後に上書き

# ケース名（順序固定）
CASE_LEVELS <- c("exp", "obs", "both", "exp_true", "obs_true", "both_true")

#──────────────────────── 2. グリッド & 真分布 ─────────────────#
# 2-1 グリッド
Y_list <- setNames(lapply(seq_len(m), \(.) seq_len(n)), paste0("Y", seq_len(m)))
grid <- do.call(expand.grid, c(Y_list, list(X = seq_len(m)), list(Y = seq_len(n))))
Z <- nrow(grid)

# 2-2 ユーティリティ（グリッド系）
monotone_idx <- function(grid, m){
  ok <- rep(TRUE, nrow(grid))
  for(i in seq_len(m-1)) ok <- ok & (grid[[paste0("Y",i)]] <= grid[[paste0("Y",i+1)]])
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
event_blocks_from_idx <- function(idx, lb = NULL, ub = NULL, grid) {
  if (is.null(idx)) return(list())
  if (is.list(idx)) idx <- unlist(idx, recursive = TRUE, use.names = FALSE)
  idx <- as.integer(idx); idx <- idx[is.finite(idx) & !is.na(idx)]
  Zloc <- nrow(grid); idx <- idx[idx >= 1 & idx <= Zloc]
  if (length(idx) == 0) return(list())
  Arow <- sparseMatrix(i = rep(1, length(idx)), j = idx, x = rep(1, length(idx)), dims = c(1, Zloc))
  out <- list()
  if (!is.null(lb)) out$lb <- list(mat = Arow, dir = ">=", rhs = lb)
  if (!is.null(ub)) out$ub <- list(mat = Arow, dir = "<=", rhs = ub)
  out
}
compile_blocks <- function(blocks){
  if (length(blocks) == 0L) {
    return(list(
      A   = Matrix::sparseMatrix(i=integer(0), j=integer(0), x=numeric(0), dims=c(0, Z)),
      dir = character(0),
      rhs = numeric(0)
    ))
  }
  mats <- lapply(blocks, `[[`, "mat")
  dirs <- lapply(blocks, `[[`, "dir")
  rhs  <- lapply(blocks, `[[`, "rhs")
  
  keep <- vapply(mats, function(A){
    if (is.null(A)) return(FALSE)
    inherits(A, "sparseMatrix") || is.matrix(A)
  }, logical(1))
  
  if (!any(keep)) {
    return(list(
      A   = Matrix::sparseMatrix(i=integer(0), j=integer(0), x=numeric(0), dims=c(0, Z)),
      dir = character(0),
      rhs = numeric(0)
    ))
  }
  
  mats <- mats[keep]; dirs <- dirs[keep]; rhs <- rhs[keep]
  mats <- lapply(mats, function(A) {
    if (!inherits(A, "sparseMatrix")) A <- as(A, "sparseMatrix")
    if (ncol(A) == 0L) Matrix::sparseMatrix(i=integer(0), j=integer(0), x=numeric(0), dims=c(0, Z)) else A
  })
  
  Aout <- do.call(rbind, mats)
  if (ncol(Aout) == 0L) {
    Aout <- Matrix::sparseMatrix(i=integer(0), j=integer(0), x=numeric(0), dims=c(nrow(Aout), Z))
  }
  
  list(
    A   = Aout,
    dir = unlist(dirs, use.names = FALSE),
    rhs = unlist(rhs,  use.names = FALSE)
  )
}

marginal_mat <- function(idx_list, Z){
  rows <- rep(seq_along(idx_list), lengths(idx_list))
  cols <- unlist(idx_list, use.names = FALSE)
  if (length(cols) == 0L) return(sparseMatrix(i = integer(0), j = integer(0), x = numeric(0), dims = c(length(idx_list), Z)))
  sparseMatrix(i = rows, j = cols, x = rep(1, length(cols)), dims = c(length(idx_list), Z))
}

# 2-3 L1/L2/L3 の「0<=差<=1」イベント
build_diff_event_indices <- function(grid, k = 1L){
  y0 <- grid$Y1; y1 <- grid$Y2; y2 <- grid$Y3
  E1 <- which((y1 - y0) >= 0 & (y1 - y0) <= k)
  E2 <- which((y2 - y1) >= 0 & (y2 - y1) <= k)
  E3 <- which((y2 - y0) >= 0 & (y2 - y0) <= k)
  list(E1=E1, E2=E2, E3=E3)
}
L_EVENTS <- build_diff_event_indices(grid, k = 1L)

# 2-4 真の PO（帯域1 + consistency）
a_xy <- matrix(c(
  0.15, 0.1, 0.1,
  0.1,  0.2, 0.1,
  0.05, 0.1, 0.1
), nrow = m, ncol = n, byrow = TRUE)
a_xy <- a_xy / sum(a_xy)
band_idx <- function(grid, m, k = 1L) {
  Y_mat <- as.matrix(grid[, paste0("Y", seq_len(m))])
  ok <- rep(TRUE, nrow(grid))
  for (s in 2:m) for (t in 1:(s-1)) {
    d <- Y_mat[, s] - Y_mat[, t]
    ok <- ok & (d >= 0 & d <= k)
  }
  which(ok)
}
k_true  <- 1L
good_idx <- setdiff(band_idx(grid, m, k_true), consistency_bad(grid, m))
denom_xy <- table(factor(grid$X[good_idx], levels = seq_len(m)), factor(grid$Y[good_idx], levels = seq_len(n)))
denom_xy <- as.matrix(denom_xy)
stopifnot(!any(denom_xy == 0))
po_prob <- numeric(Z)
ix <- good_idx
po_prob[ix] <- a_xy[cbind(grid$X[ix], grid$Y[ix])] / denom_xy[cbind(grid$X[ix], grid$Y[ix])]
stopifnot(abs(sum(po_prob) - 1) < 1e-12)

# 2-5 周辺用インデックス（実験・観測）
idx_exp <- idx_obs <- vector("list", m*n)
cnt <- 1
for(k in seq_len(m)) for(y in seq_len(n)){
  idx_exp[[cnt]] <- which(grid[[paste0("Y",k)]] == y)
  idx_obs[[cnt]] <- which(grid$X==k & grid$Y==y)
  cnt <- cnt + 1
}
.NM_EXP <- sprintf("exp_k%d_y%d", rep(seq_len(m), each=n), rep(seq_len(n), m))
.NM_OBS <- sprintf("obs_k%d_y%d", rep(seq_len(m), each=n), rep(seq_len(n), m))
names(idx_exp) <- .NM_EXP; names(idx_obs) <- .NM_OBS
mat_exp <- marginal_mat(idx_exp, Z)
mat_obs <- marginal_mat(idx_obs, Z)

# 2-6 base（確率合計=1、consistency=0は境界で処理）
UB0_IDX <- consistency_bad(grid, m) # ← 上限0にする対象インデックス
base_blocks <- list(
  sum = list(
    mat = Matrix::sparseMatrix(
      i    = rep.int(1L, Z),
      j    = seq_len(Z),
      x    = rep.int(1, Z),
      dims = c(1L, Z)
    ),
    dir = "==",
    rhs = 1
  )
)

#──────────────────────── 3. 一度だけ bounds を作成 ─────────────#
make_bounds <- function(Z_len, ub0_idx = integer(0)) {
  ub <- rep(1, Z_len)
  if (length(ub0_idx)) ub[ub0_idx] <- 0
  list(
    lower = list(ind = seq_len(Z_len), val = rep(0, Z_len)),
    upper = list(ind = seq_len(Z_len), val = ub)
  )
}
BOUNDS_GLOBAL <- make_bounds(Z, UB0_IDX)

#──────────────────────── 4. 目的関数 ──────────────────────────#
make_obj <- function(obj_spec, grid){
  Z <- nrow(grid)
  v <- rep(TRUE, Z)
  apply_conditions <- function(v, grid, conds){
    for(cond in conds){
      Yi <- grid[[paste0("Y", cond$var)]]
      v  <- v & switch(cond$op,
                       "==" = Yi == cond$val, "<" = Yi < cond$val, "<=" = Yi <= cond$val,
                       ">" = Yi > cond$val,  ">=" = Yi >= cond$val, stop("unsupported op"))
    }
    v
  }
  if (obj_spec$type == "conditional") {
    if (!is.null(obj_spec$target_eq)) {
      eq_idx <- which(!is.na(obj_spec$target_eq))
      eq_list <- lapply(eq_idx, function(i) list(var=i, op="==", val=obj_spec$target_eq[i]))
      v <- apply_conditions(v, grid, eq_list)
    }
    if (!is.null(obj_spec$target_ineq)) v <- apply_conditions(v, grid, obj_spec$target_ineq)
    if (!is.null(obj_spec$condX)) v <- v & (grid$X == obj_spec$condX)
    if (!is.null(obj_spec$condY)) v <- v & (grid$Y == obj_spec$condY)
    obj_vec <- as.integer(v)
    denom_lab <- NULL
    if (!is.null(obj_spec$condX) && !is.null(obj_spec$condY)) denom_lab <- sprintf("obs_k%d_y%d", obj_spec$condX, obj_spec$condY)
    else if (!is.null(obj_spec$condX)) denom_lab <- sprintf("obs_k%d_yALL", obj_spec$condX)
    else if (!is.null(obj_spec$condY)) denom_lab <- sprintf("obs_kALL_y%d", obj_spec$condY)
    list(obj_vec=obj_vec, denom_lab=denom_lab, obj_label="P(…|…)")
  } else if (obj_spec$type == "joint") {
    if (!is.null(obj_spec$target_eq)) {
      eq_idx <- which(!is.na(obj_spec$target_eq))
      eq_list <- lapply(eq_idx, function(i) list(var=i, op="==", val=obj_spec$target_eq[i]))
      v <- apply_conditions(v, grid, eq_list)
    }
    if (!is.null(obj_spec$target_ineq)) v <- apply_conditions(v, grid, obj_spec$target_ineq)
    if (!is.null(obj_spec$condX)) v <- v & (grid$X == obj_spec$condX)
    if (!is.null(obj_spec$condY)) v <- v & (grid$Y == obj_spec$condY)
    obj_vec <- as.integer(v)
    list(obj_vec=obj_vec, denom_lab=NULL, obj_label="P(…)")
  } else if (obj_spec$type == "linear") {
    Zloc <- nrow(grid)
    cond_mask <- rep(TRUE, Zloc)
    if (!is.null(obj_spec$condX)) cond_mask <- cond_mask & (grid$X == obj_spec$condX)
    if (!is.null(obj_spec$condY)) cond_mask <- cond_mask & (grid$Y == obj_spec$condY)
    intercept <- if (!is.null(obj_spec$intercept)) as.numeric(obj_spec$intercept) else 0
    zero_based <- isTRUE(obj_spec$zero_based)
    y_mat <- sapply(seq_len(m), function(k) {
      vals <- as.numeric(grid[[paste0("Y", k)]])
      if (zero_based) vals <- vals - 1
      vals
    })
    w <- rep(intercept, Zloc) + as.numeric(y_mat %*% as.numeric(obj_spec$var_coefs))
    w_num <- w; w_num[!cond_mask] <- 0
    denom_lab <- NULL
    if (!is.null(obj_spec$condX) && !is.null(obj_spec$condY)) denom_lab <- sprintf("obs_k%d_y%d", obj_spec$condX, obj_spec$condY)
    else if (!is.null(obj_spec$condX)) denom_lab <- sprintf("obs_k%d_yALL", obj_spec$condX)
    else if (!is.null(obj_spec$condY)) denom_lab <- sprintf("obs_kALL_y%d", obj_spec$condY)
    list(obj_vec=w_num, denom_lab=denom_lab, obj_label=ifelse(is.null(obj_spec$label_override),"E[g(Y)]",obj_spec$label_override))
  } else stop("unknown obj type")
}

# 例：目的関数
obj_specs <- list(
  "P(Y0=0,Y1=0,Y2=1)" = list(type="joint", target_eq=c(1,1,2), target_ineq=NULL, condX=NULL, condY=NULL),
  "E[Y1-Y0 | X=2,Y=2]" = list(type="linear", var_coefs=c(-1,1,0), intercept=0, zero_based=TRUE, condX=3, condY=3, label_override="E[Y1-Y0|X=2,Y=2]"),
  "P(Y0=1,Y1=0,Y2=1,X=1,Y=0)" = list(type="joint", target_eq=c(2,1,2), target_ineq=NULL, condX=2, condY=1)
)

# 分母インデックス
parse_obs_denom_lab <- function(lab, m, n) {
  m1 <- regexec("^obs_k(\\d+)_y(\\d+)$", lab); r1 <- regmatches(lab, m1)[[1]]
  if (length(r1) == 3) { k <- as.integer(r1[2]); y <- as.integer(r1[3]); return(list(idx=(k-1L)*n+y)) }
  m2 <- regexec("^obs_k(\\d+)_yALL$", lab); r2 <- regmatches(lab, m2)[[1]]
  if (length(r2) == 2) { k <- as.integer(r2[2]); return(list(idx=((k-1L)*n+1L):((k-1L)*n+n))) }
  m3 <- regexec("^obs_kALL_y(\\d+)$", lab); r3 <- regmatches(lab, m3)[[1]]
  if (length(r3) == 2) { y <- as.integer(r3[2]); return(list(idx=(0:(m-1L))*n + y)) }
  list(idx=integer(0))
}
collect_obs_denom_indices <- function(obj_specs, grid, m, n) {
  labs <- unique(na.omit(unlist(lapply(names(obj_specs), function(nm){
    sp <- obj_specs[[nm]]; mm <- make_obj(sp, grid); if (!is.null(mm$denom_lab)) mm$denom_lab else NA_character_
  }))))
  out <- list()
  for (lab in labs) out[[lab]] <- parse_obs_denom_lab(lab, m, n)$idx
  out
}
OBS_DENOM_IDX_LIST <- collect_obs_denom_indices(obj_specs, grid, m, n)
.denom_ok_factory <- function(denom_idx_list) {
  function(pXY) {
    if (!length(denom_idx_list)) return(TRUE)
    for (idx in denom_idx_list) if (sum(pXY[idx]) <= 0) return(FALSE)
    TRUE
  }
}

#──────────────────────── 5. GLPK 入出力ユーティリティ ──────────#
.to_stm <- function(A, nvar){
  if (is.null(A)) stop("to_stm: A is NULL")
  if (inherits(A, "simple_triplet_matrix")) return(A)
  if (inherits(A, "sparseMatrix")) {
    ts <- Matrix::summary(A)  # data.frame(i, j, x) with 1-based indices
    return(slam::simple_triplet_matrix(
      i = ts$i,
      j = ts$j,
      v = as.numeric(ts$x),
      nrow = nrow(A),
      ncol = if (ncol(A) == 0L) nvar else ncol(A)
    ))
  }
  if (is.matrix(A)) return(slam::as.simple_triplet_matrix(A))
  stop("to_stm: unsupported matrix type")
}


#──────────────────────── 6. L1/L2/L3 制約テンプレ（slam 同梱） ──#
.CMP_CACHE <- new.env(parent = emptyenv())

compile_lp_template_L123 <- function(sname, sc, grid, mat_exp, mat_obs){
  key <- paste("L123", sname, nrow(grid), ncol(mat_exp), ncol(mat_obs), sep="|")
  if (!is.null(.CMP_CACHE[[key]])) return(.CMP_CACHE[[key]])
  
  base_comp <- compile_blocks(base_blocks)
  rel_blks <- list()
  rel_blks <- c(rel_blks, event_blocks_from_idx(L_EVENTS$E1, lb=sc$L_vals[1], ub=NULL, grid))
  rel_blks <- c(rel_blks, event_blocks_from_idx(L_EVENTS$E2, lb=sc$L_vals[2], ub=NULL, grid))
  rel_blks <- c(rel_blks, event_blocks_from_idx(L_EVENTS$E3, lb=sc$L_vals[3], ub=NULL, grid))
  rel_comp <- compile_blocks(rel_blks)
  
  Zloc <- nrow(grid)
  normalize_A <- function(A, Z){
    if (!inherits(A, "sparseMatrix")) A <- as(A, "sparseMatrix")
    if (ncol(A) == 0L) Matrix::sparseMatrix(i = integer(0), j = integer(0), x = numeric(0), dims = c(0, Z)) else A
  }
  baseA <- normalize_A(base_comp$A, Zloc)
  relA  <- normalize_A(rel_comp$A,  Zloc)
  
  build_case <- function(case_name){
    if (case_name == "exp") {
      margA <- mat_exp
      A  <- rbind(baseA, relA, margA)
      dir <- c(base_comp$dir, rel_comp$dir, rep("==", nrow(margA)))
      rhs <- c(base_comp$rhs, rel_comp$rhs, rep(NA_real_, nrow(margA)))
      rows_exp <- seq.int(length(rhs) - nrow(margA) + 1L, length(rhs))
      rows_obs <- integer(0)
    } else if (case_name == "obs") {
      margA <- mat_obs
      A  <- rbind(baseA, relA, margA)
      dir <- c(base_comp$dir, rel_comp$dir, rep("==", nrow(margA)))
      rhs <- c(base_comp$rhs, rel_comp$rhs, rep(NA_real_, nrow(margA)))
      rows_exp <- integer(0)
      rows_obs <- seq.int(length(rhs) - nrow(margA) + 1L, length(rhs))
    } else { # both
      margA <- rbind(mat_exp, mat_obs)
      if (ncol(margA) == 0L) {
        margA <- Matrix::sparseMatrix(i=integer(0), j=integer(0), x=numeric(0), dims=c(0, Zloc))
      }
      A  <- rbind(baseA, relA, margA)
      dir <- c(base_comp$dir, rel_comp$dir, rep("==", nrow(margA)))
      rhs <- c(base_comp$rhs, rel_comp$rhs, rep(NA_real_, nrow(margA)))
      rows_all <- seq.int(length(rhs) - nrow(margA) + 1L, length(rhs))
      rows_exp <- head(rows_all, nrow(mat_exp))
      rows_obs <- tail(rows_all, nrow(mat_obs))
    }
    A_stm <- .to_stm(A, Zloc)
    list(A = A, A_stm = A_stm, dir = dir, rhs_template = rhs,
         marg_rows_exp = rows_exp, marg_rows_obs = rows_obs)
  }
  
  tpl <- list(
    exp  = build_case("exp"),
    obs  = build_case("obs"),
    both = build_case("both")
  )
  .CMP_CACHE[[key]] <- tpl
  tpl
}

#──────────────────────── 7. GLPK 呼び出し（簡素） ───────────────#
.solve_once_glpk <- function(obj, mat_stm, dir, rhs, maximise = FALSE) {
  ctrl1 <- list(canonicalize_status=TRUE, presolve=TRUE,  verbose=FALSE, tm_limit=0L)
  ctrl2 <- list(canonicalize_status=TRUE, presolve=FALSE, verbose=FALSE, tm_limit=0L)
  sol <- Rglpk::Rglpk_solve_LP(obj=obj, mat=mat_stm, dir=dir, rhs=rhs,
                               bounds=BOUNDS_GLOBAL, max=maximise, control=ctrl1)
  if (!is.null(sol$status) && sol$status == 0) return(sol)
  Rglpk::Rglpk_solve_LP(obj=obj, mat=mat_stm, dir=dir, rhs=rhs,
                        bounds=BOUNDS_GLOBAL, max=maximise, control=ctrl2)
}
solve_with_tpl <- function(obj_vec, tpl_case, rhs, maximise) {
  .solve_once_glpk(obj = obj_vec, mat_stm = tpl_case$A_stm, dir = tpl_case$dir, rhs = rhs, maximise = maximise)
}

#──────────────────────── 8. サンプリング（split2N のみ） ───────#
MAX_DRAWS_PER_SAMPLE <- 1e7
ensure_sampling_bank_split2N <- function(N, M, denom_idx_list = list()) {
  denom_ok <- .denom_ok_factory(denom_idx_list)
  res <- vector("list", M)
  for (i in seq_len(M)) {
    tries <- 0L
    repeat {
      tries <- tries + 1L
      idx_all <- sample.int(Z, size = as.integer(2L*N), replace = TRUE, prob = po_prob)
      idx_exp <- idx_all[seq_len(N)]
      idx_obs <- idx_all[seq.int(N+1L, 2L*N)]
      pY_list_i <- lapply(seq_len(m), function(k) {
        yk <- grid[[paste0("Y", k)]][idx_exp]
        as.numeric(tabulate(yk, nbins = n)) / as.integer(N)
      })
      bins <- (as.integer(grid$X[idx_obs]) - 1L) * n + as.integer(grid$Y[idx_obs])
      cnt  <- as.numeric(tabulate(bins, nbins = m*n))
      pXY_i <- cnt / as.integer(N)
      if (denom_ok(pXY_i)) {
        res[[i]] <- list(pY_list = pY_list_i, pXY = pXY_i, exp_id = i, obs_id = i)
        break
      }
      if (tries >= MAX_DRAWS_PER_SAMPLE) stop("split2N: feasible sample not found (denom>0 required).")
    }
  }
  res
}

#──────────────────────── 9. 最適化（逐次・簡素） ────────────────#
run_for_obj <- function(obj_spec, spec_name, b_exp, b_obs, scenarios = constraint_scenarios){
  obj <- make_obj(obj_spec, grid)
  
  cases <- c("exp", "obs", "both")  # 必ず両方与える前提
  result_tbl <- data.frame(
    scenario=character(), case=character(), L1=numeric(), L2=numeric(), L3=numeric(),
    min_val=numeric(), max_val=numeric(), min_status=integer(), max_status=integer(),
    stringsAsFactors = FALSE
  )
  
  scen_order <- names(scenarios)
  for (sname in scen_order) {
    sc       <- scenarios[[sname]]
    tpl_all  <- compile_lp_template_L123(sname, sc, grid, mat_exp, mat_obs)
    
    for (cname in cases) {
      tpl <- tpl_all[[cname]]
      rhs <- tpl$rhs_template
      if (cname %in% c("exp","both") && length(tpl$marg_rows_exp) > 0) {
        stopifnot(length(b_exp) == length(tpl$marg_rows_exp))
        rhs[tpl$marg_rows_exp] <- as.numeric(b_exp)
      }
      if (cname %in% c("obs","both") && length(tpl$marg_rows_obs) > 0) {
        stopifnot(length(b_obs) == length(tpl$marg_rows_obs))
        rhs[tpl$marg_rows_obs] <- as.numeric(b_obs)
      }
      if (anyNA(rhs)) stop(sprintf("run_for_obj: rhs contains NA (case=%s, scenario=%s)", cname, sname))
      
      sol_min <- solve_with_tpl(obj_vec = obj$obj_vec, tpl_case = tpl, rhs = rhs, maximise = FALSE)
      sol_max <- solve_with_tpl(obj_vec = obj$obj_vec, tpl_case = tpl, rhs = rhs, maximise = TRUE)
      
      denom <- 1
      if (!is.null(obj$denom_lab)) {
        if (obj$denom_lab %in% names(idx_obs)) {
          pi <- parse_obs_denom_lab(obj$denom_lab, m, n)$idx
          denom <- sum(as.numeric(b_obs)[pi])
        } else {
          denom <- NA_real_
        }
      }
      res_min <- if (!is.null(obj$denom_lab)) ifelse(denom>0, sol_min$optimum/denom, NA_real_) else sol_min$optimum
      res_max <- if (!is.null(obj$denom_lab)) ifelse(denom>0, sol_max$optimum/denom, NA_real_) else sol_max$optimum
      
      result_tbl <- rbind(result_tbl, data.frame(
        scenario=sname, case=cname, L1=sc$L_vals[1], L2=sc$L_vals[2], L3=sc$L_vals[3],
        min_val=res_min, max_val=res_max, min_status=sol_min$status, max_status=sol_max$status,
        stringsAsFactors = FALSE
      ))
    }
  }
  list(results = result_tbl)
}

split_replicates <- function(rep_df) {
  scenario_levels <- names(constraint_scenarios)
  scenario_levels <- scenario_levels[scenario_levels %in% rep_df$scenario]
  rep_df <- rep_df |>
    mutate(scenario=factor(scenario, levels=scenario_levels),
           case=factor(case, levels=CASE_LEVELS))
  by_scn <- split(rep_df, rep_df$scenario); by_scn <- by_scn[scenario_levels]
  lapply(by_scn, function(df_s) {
    by_case <- split(df_s, df_s$case); by_case <- by_case[CASE_LEVELS[1:3]]
    lapply(by_case, function(x) {
      if (nrow(x) == 0) return(as.data.frame(x))
      cols <- c("rep", "min_val", "max_val", "exp_id", "obs_id")
      y <- x[, intersect(cols, names(x)), drop = FALSE]; rownames(y) <- NULL; as.data.frame(y)
    })
  })
}

simulate_simple <- function(obj_name, obj_spec, N, M, draws_exp, draws_obs) {
  safe_mean <- function(x) if (all(is.na(x))) NA_real_ else mean(x, na.rm = TRUE)
  safe_q    <- function(x, p) if (all(is.na(x))) NA_real_ else as.numeric(stats::quantile(x, probs = p, na.rm = TRUE, names = FALSE))
  
  reps <- vector("list", M)
  for (r in seq_len(M)) {
    b_exp <- unlist(draws_exp[[r]]$pY_list, use.names = FALSE); names(b_exp) <- .NM_EXP
    b_obs <- as.numeric(draws_obs[[r]]$pXY);                   names(b_obs) <- .NM_OBS
    out   <- run_for_obj(obj_spec, obj_name, b_exp = b_exp, b_obs = b_obs, scenarios = constraint_scenarios)
    df <- out$results |>
      dplyr::mutate(
        feasible = (min_status == 0 & max_status == 0),
        feasible = dplyr::coalesce(feasible, FALSE),
        min_val  = ifelse(feasible, min_val, NA_real_),
        max_val  = ifelse(feasible, max_val, NA_real_),
        rep   = r,
        exp_id = draws_exp[[r]]$exp_id,
        obs_id = draws_obs[[r]]$obs_id
      ) |>
      dplyr::select(scenario, L1, L2, L3, case, feasible, min_val, max_val, rep, exp_id, obs_id)
    reps[[r]] <- df
  }
  rep_df <- dplyr::bind_rows(reps)
  reps_nested <- split_replicates(rep_df)
  
  summary_df <- rep_df |>
    dplyr::mutate(scenario = factor(scenario, levels = names(constraint_scenarios)),
                  case     = factor(case, levels = CASE_LEVELS[1:3])) |>
    dplyr::group_by(scenario, L1, L2, L3, case) |>
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
  
  # 真値（1回）
  pXY_true <- as.vector(t(tapply(po_prob, list(grid$X, grid$Y), sum)))
  pY_list_true <- lapply(seq_len(m), function(k) as.numeric(tapply(po_prob, grid[[paste0("Y", k)]], sum)))
  b_obs_true <- pXY_true; names(b_obs_true) <- .NM_OBS
  b_exp_true <- unlist(pY_list_true); names(b_exp_true) <- .NM_EXP
  out_true <- run_for_obj(obj_spec, obj_name, b_exp = b_exp_true, b_obs = b_obs_true)
  true_rows <- out_true$results |>
    dplyr::select(scenario, L1, L2, L3, case, min_val, max_val) |>
    dplyr::mutate(
      case     = paste0(as.character(case), "_true"),
      mean_lb  = min_val, ci_lb_lo = min_val, ci_lb_hi = min_val,
      mean_ub  = max_val, ci_ub_lo = max_val, ci_ub_hi = max_val
    ) |>
    dplyr::select(scenario, L1, L2, L3, case, mean_lb, ci_lb_lo, ci_lb_hi, mean_ub, ci_ub_lo, ci_ub_hi)
  
  summary_df <- dplyr::bind_rows(summary_df, true_rows) |>
    dplyr::mutate(scenario = factor(scenario, levels = names(constraint_scenarios)),
                  case     = factor(case,     levels = CASE_LEVELS)) |>
    dplyr::arrange(scenario, case)
  
  true_val <- { mm <- make_obj(obj_spec, grid); numer <- sum(mm$obj_vec * po_prob); denom <- 1
  if (!is.null(mm$denom_lab)) {
    pi <- parse_obs_denom_lab(mm$denom_lab, m, n)$idx; denom <- sum(pXY_true[pi])
    if (!is.finite(denom) || denom <= 0) denom <- NA_real_
  }
  ifelse(is.na(denom), NA_real_, numer/denom)
  }
  summary_df <- dplyr::mutate(summary_df, true = true_val)
  
  list(replicates = reps_nested, summary = as.data.frame(summary_df))
}

#──────────────────────── 10. スイープ（逐次・単純化） ───────────#
scenario_name_L <- function(L1,L2,L3) sprintf("(L1,L2,L3)=(%.3f,%.3f,%.3f)", L1, L2, L3)
make_L123_scenario <- function(L1, L2, L3) list(idx_list=NULL, L_vals=c(L1=L1, L2=L2, L3=L3))
make_Lgrid_scenarios <- function(L1_seq, L2_seq, L3_seq){
  sc_list <- list()
  for (L1 in L1_seq) for (L2 in L2_seq) for (L3 in L3_seq) sc_list[[scenario_name_L(L1,L2,L3)]] <- make_L123_scenario(L1,L2,L3)
  sc_list
}

run_L123_sweep_simple <- function(L1_seq, L2_seq, L3_seq,
                                  obj_specs, N, M) {
  # 1) シナリオ確定（グローバルと同名オブジェクトを上書き）
  assign("constraint_scenarios", make_Lgrid_scenarios(L1_seq, L2_seq, L3_seq), envir = .GlobalEnv)
  
  # 2) サンプリング（split2N 固定）を一度だけ作って全オブジェクトで共有
  pack <- ensure_sampling_bank_split2N(N, M, denom_idx_list = OBS_DENOM_IDX_LIST)
  draws_exp <- lapply(seq_len(M), function(r) list(pY_list = pack[[r]]$pY_list, exp_id = r))
  draws_obs <- lapply(seq_len(M), function(r) list(pXY     = pack[[r]]$pXY,     obs_id = r))
  
  # 3) LP テンプレ一括作成（slam を添付）
  for (sname in names(constraint_scenarios)) {
    invisible(compile_lp_template_L123(sname, constraint_scenarios[[sname]], grid, mat_exp, mat_obs))
  }
  
  # 4) 各オブジェクトで逐次評価
  out <- list()
  for (obj_name in names(obj_specs)) {
    obj_spec <- obj_specs[[obj_name]]
    res <- simulate_simple(obj_name, obj_spec, N, M, draws_exp, draws_obs)
    
    combo_key <- sprintf("Nexp=%d_Nobs=%d", N, N)
    M_key     <- sprintf("M=%d", M)
    if (is.null(out[[obj_name]])) out[[obj_name]] <- list()
    if (is.null(out[[obj_name]][[combo_key]])) out[[obj_name]][[combo_key]] <- list()
    out[[obj_name]][[combo_key]][[M_key]] <- res
  }
  
  # 5) 既存の大きなストアに格納（出力・tex 互換）
  put_runs_into_consolidated_Lgrid(out)
  invisible(out)
}

#──────────────────────── 11. ストアと集約 ─────────────────────#
`0912Revised_RESULT_simulation_L1L2L3` <- list()

put_runs_into_consolidated_Lgrid <- function(new_out){
  for (obj_name in names(new_out)) {
    if (is.null(`0912Revised_RESULT_simulation_L1L2L3`[[obj_name]]))
      `0912Revised_RESULT_simulation_L1L2L3`[[obj_name]] <<- list()
    if (is.null(`0912Revised_RESULT_simulation_L1L2L3`[[obj_name]]$summary_all))
      `0912Revised_RESULT_simulation_L1L2L3`[[obj_name]]$summary_all <<- data.frame()
    
    for (combo_key in names(new_out[[obj_name]])) {
      Nexp_val <- as.integer(sub("^Nexp=([0-9]+).*", "\\1", combo_key))
      Nobs_val <- as.integer(sub("^Nexp=[0-9]+_Nobs=([0-9]+).*", "\\1", combo_key))
      for (M_key in names(new_out[[obj_name]][[combo_key]])) {
        M_val <- as.integer(sub("^M=([0-9]+)$", "\\1", M_key))
        res   <- new_out[[obj_name]][[combo_key]][[M_key]]
        
        if (is.null(`0912Revised_RESULT_simulation_L1L2L3`[[obj_name]][[combo_key]]))
          `0912Revised_RESULT_simulation_L1L2L3`[[obj_name]][[combo_key]] <<- list()
        if (is.null(`0912Revised_RESULT_simulation_L1L2L3`[[obj_name]][[combo_key]][[M_key]]))
          `0912Revised_RESULT_simulation_L1L2L3`[[obj_name]][[combo_key]][[M_key]] <<- list(replicates = res$replicates, summary = data.frame())
        `0912Revised_RESULT_simulation_L1L2L3`[[obj_name]][[combo_key]][[M_key]]$replicates <<- res$replicates
        `0912Revised_RESULT_simulation_L1L2L3`[[obj_name]][[combo_key]][[M_key]]$summary    <<-
          dplyr::bind_rows(
            `0912Revised_RESULT_simulation_L1L2L3`[[obj_name]][[combo_key]][[M_key]]$summary,
            res$summary
          ) |>
          dplyr::distinct(scenario, L1, L2, L3, case, .keep_all = TRUE) |>
          dplyr::arrange(scenario, case)
        
        sumdf <- res$summary
        if (!is.null(sumdf) && nrow(sumdf) > 0) {
          sumdf$Nexp <- Nexp_val; sumdf$Nobs <- Nobs_val; sumdf$M <- M_val
          old_big <- `0912Revised_RESULT_simulation_L1L2L3`[[obj_name]]$summary_all
          new_big <- dplyr::bind_rows(old_big, sumdf) |>
            dplyr::distinct(Nexp, Nobs, M, scenario, L1, L2, L3, case, .keep_all = TRUE) |>
            dplyr::arrange(Nexp, Nobs, M, scenario, case)
          `0912Revised_RESULT_simulation_L1L2L3`[[obj_name]]$summary_all <<- new_big
        }
      }
    }
  }
}

collect_L123_summaries <- function() {
  if (!exists("`0912Revised_RESULT_simulation_L1L2L3`", inherits = TRUE)) return(data.frame())
  store <- get("`0912Revised_RESULT_simulation_L1L2L3`")
  if (length(store) == 0) return(data.frame())
  out <- list()
  for (obj in names(store)) {
    df <- store[[obj]]$summary_all
    if (!is.null(df) && nrow(df)) { df$obj <- obj; out[[length(out)+1]] <- df }
  }
  if (!length(out)) return(data.frame())
  dplyr::bind_rows(out)
}

#──────────────────────── 12. TikZ/pgfplots 出力（互換のまま） ──#
if (!exists(".ensure_dir", inherits = TRUE)) {
  .ensure_dir <- function(path) dir.create(path, recursive = TRUE, showWarnings = FALSE)
}
if (!exists(".slugify", inherits = TRUE)) {
  .slugify <- function(x) {
    x <- gsub("\\s+", "-", x)
    x <- gsub("[^A-Za-z0-9._-]+", "-", x)
    x <- gsub("-+", "-", x)
    x <- gsub("(^-|-$)", "", x)
    tolower(x)
  }
}
get_summary_from_store <- function(store, obj_name, Nexp, Nobs, M) {
  ckey <- sprintf("Nexp=%d_Nobs=%d", as.integer(Nexp), as.integer(Nobs))
  mkey <- sprintf("M=%d", as.integer(M))
  stopifnot(is.list(store), obj_name %in% names(store))
  stopifnot(ckey %in% names(store[[obj_name]]))
  stopifnot(mkey %in% names(store[[obj_name]][[ckey]]))
  sumdf <- store[[obj_name]][[ckey]][[mkey]]$summary
  if (is.null(sumdf) || !is.data.frame(sumdf) || nrow(sumdf) == 0)
    stop("summary が見つからない / 空です: ", obj_name, " ", ckey, " ", mkey)
  sumdf
}
export_tikz_heatmap_tabular <- function(
    df, L3_val, case_for_values = "both",
    value = c("mean_lb","mean_ub","feasible_rate"),
    L_vals = NULL, L3_mode = c("eq","le"),
    digits = 3, out_dir = file.path("tikz","L1L2L3"),
    file_stub = "heatmap_L1L2",
    title_prefix = NULL, colormap = "viridis",
    vmin = NULL, vmax = NULL, show_numbers = FALSE
){
  value <- match.arg(value); L3_mode <- match.arg(L3_mode)
  .fmt <- function(x, d=digits) ifelse(is.na(x), "nan", sprintf(paste0("%.", d, "f"), x))
  .fmt_axis <- function(x, d=digits) sprintf(paste0("%.", d, "f"), x)
  
  base <- df[df$case == case_for_values & !grepl("_true$", df$case), , drop = FALSE]
  if (nrow(base) == 0) {
    base <- df[df$case == paste0(case_for_values, "_true"), , drop = FALSE]
    base$case <- sub("_true$", "", base$case)
  }
  if (nrow(base) == 0) stop("指定 case の行が見つかりません: ", case_for_values)
  
  eps <- 10^(-(digits+1))
  if (L3_mode == "eq") {
    x <- base[abs(base$L3 - L3_val) < eps, , drop = FALSE]
  } else {
    x <- base[base$L3 <= L3_val + eps, , drop = FALSE]
    if (nrow(x) > 0) {
      x <- x |>
        dplyr::group_by(L1, L2) |>
        dplyr::slice_max(L3, n = 1, with_ties = FALSE) |>
        dplyr::ungroup()
    }
  }
  if (nrow(x) == 0) stop("指定 L3 条件に合致する行がありません。")
  
  if (is.null(L_vals)) {
    L1_vals <- sort(unique(round(base$L1, digits)))
    L2_vals <- sort(unique(round(base$L2, digits)))
  } else {
    L1_vals <- L_vals
    L2_vals <- L_vals
  }
  
  pick_val <- function(L1v, L2v, col) {
    row <- x[abs(x$L1 - L1v) < eps & abs(x$L2 - L2v) < eps, , drop = FALSE]
    if (nrow(row) == 0) return(NA_real_)
    as.numeric(row[[col]][1])
  }
  tbl_lines <- c("x y z")
  for (L2v in L2_vals) {
    for (L1v in L1_vals) {
      v <- pick_val(L1v, L2v, value)
      tbl_lines <- c(tbl_lines, paste(.fmt_axis(L1v), .fmt_axis(L2v), .fmt(v)))
    }
  }
  table_block <- paste(paste(tbl_lines, collapse = "\n"), "\n", sep = "")
  
  if (is.null(title_prefix)) {
    title_prefix <- switch(case_for_values, exp="Exp.", obs="Obs.", both="Both", paste0("case=", case_for_values))
  }
  title_line <- if (L3_mode == "eq") {
    sprintf("%s  \\quad $L_3 = %s$", title_prefix, .fmt_axis(L3_val))
  } else {
    sprintf("%s  \\quad $L_3 \\le %s$", title_prefix, .fmt_axis(L3_val))
  }
  xticks <- paste(.fmt_axis(L1_vals), collapse = ",")
  yticks <- paste(.fmt_axis(L2_vals), collapse = ",")
  
  pm_min <- if (is.null(vmin)) "" else sprintf("point meta min=%s,", .fmt_axis(vmin))
  pm_max <- if (is.null(vmax)) "" else sprintf("point meta max=%s,", .fmt_axis(vmax))
  
  overlay_nodes <- ""
  if (isTRUE(show_numbers)) {
    lines <- c()
    for (L2v in L2_vals) for (L1v in L1_vals) {
      v <- pick_val(L1v, L2v, value)
      if (is.finite(v)) {
        lines <- c(lines, sprintf("\\node at (axis cs:%s,%s) {\\scriptsize %s};",
                                  .fmt_axis(L1v), .fmt_axis(L2v), .fmt(v, digits)))
      }
    }
    overlay_nodes <- paste(lines, collapse = "\n    ")
  }
  
  tikz <- sprintf("
%% Auto-generated TikZ heatmap (pgfplots) for %s / value=%s
\\begin{tikzpicture}
  \\begin{axis}[
    width=12cm, height=10cm,
    title={%s},
    xlabel={$L_1$}, ylabel={$L_2$},
    xtick={%s}, ytick={%s},
    tick label style={/pgf/number format/fixed,/pgf/number format/precision=%d},
    enlargelimits=false,
    grid=both,
    colorbar,
    colormap/%s,
    %s %s
  ]
    \\addplot [matrix plot*, point meta=explicit, mesh/cols=%d] table [x=x, y=y, meta=z, row sep=\\n] {
%s    };
%s
  \\end{axis}
\\end{tikzpicture}
", deparse(substitute(df)), value, title_line, xticks, yticks, digits, colormap, pm_min, pm_max, length(L1_vals), table_block, overlay_nodes)
  
  .ensure_dir(out_dir)
  fstub <- paste0(file_stub, "_", value,
                  "_", if (L3_mode=="eq") paste0("L3eq", gsub("\\.", "p", .fmt_axis(L3_val))) else paste0("L3le", gsub("\\.", "p", .fmt_axis(L3_val))),
                  "_case-", case_for_values)
  fn <- file.path(out_dir, paste0(fstub, ".tex"))
  writeLines(tikz, fn, useBytes = TRUE)
  invisible(list(path = normalizePath(fn, mustWork = FALSE),
                 meta = list(case = case_for_values, value = value, L3 = L3_val, L3_mode = L3_mode),
                 tikz = tikz))
}
export_tikz_heatmap_from_store <- function(
    store, obj_name, N, M,
    L3_val,
    case_for_values = "both",
    value = c("mean_lb","mean_ub","feasible_rate"),
    L_vals = NULL,
    L3_mode = c("eq","le"),
    digits = 3,
    out_dir = file.path("tikz","L1L2L3"),
    colormap = "viridis",
    vmin = NULL, vmax = NULL,
    show_numbers = FALSE
){
  df <- get_summary_from_store(store, obj_name, Nexp = N, Nobs = N, M = M)
  if (is.null(L_vals)) {
    L_vals <- sort(unique(round(df$L1, digits)))
  }
  if (missing(value)) value <- "mean_lb"
  export_tikz_heatmap_tabular(
    df = df, L3_val = L3_val, case_for_values = case_for_values,
    value = match.arg(value), L_vals = L_vals, L3_mode = match.arg(L3_mode),
    digits = digits, out_dir = out_dir,
    file_stub = paste0("heatmap_", .slugify(obj_name), "_N", N, "_M", M),
    title_prefix = switch(case_for_values, exp="Exp.", obs="Obs.", both="Both", paste0("case=", case_for_values)),
    colormap = colormap, vmin = vmin, vmax = vmax, show_numbers = show_numbers
  )
}
export_tikz_heatmaps_and_master <- function(
    store,
    obj_names, N_values, M_values, L3_values,
    cases = c("both"),
    values = c("mean_lb","mean_ub"),
    L_vals = NULL,
    L3_mode = "eq",
    digits = 3,
    out_dir = file.path("tikz","L1L2L3"),
    master_filename = NULL,
    colormap = "viridis",
    vmin = NULL, vmax = NULL,
    show_numbers = FALSE
){
  .ensure_dir(out_dir)
  outs <- list()
  for (obj in obj_names) for (N in N_values) for (M in M_values) {
    for (cs in cases) for (vv in values) for (L3v in L3_values) {
      res <- export_tikz_heatmap_from_store(
        store = store, obj_name = obj, N = N, M = M,
        L3_val = L3v, case_for_values = cs, value = vv,
        L_vals = L_vals, L3_mode = L3_mode, digits = digits,
        out_dir = out_dir, colormap = colormap, vmin = vmin, vmax = vmax,
        show_numbers = show_numbers
      )
      outs[[length(outs)+1]] <- c(res, meta = list(obj=obj, N=N, M=M, case=cs, value=vv, L3=L3v, mode=L3_mode))
    }
  }
  
  if (is.null(master_filename)) {
    scope_tag <- paste0("N", paste(N_values, collapse="+"),
                        "_M", paste(M_values, collapse="+"),
                        "_", L3_mode)
    master_filename <- file.path(out_dir, paste0("tikz_all_", scope_tag, ".tex"))
  }
  con <- file(master_filename, open = "wb"); on.exit(close(con), add = TRUE)
  writeLines("% === Auto-generated TikZ heatmaps ===", con, useBytes = TRUE)
  for (it in outs) {
    cap <- sprintf("\\noindent\\textbf{Objective: %s}\\\\ N=%d, M=%d, case=%s, value=%s, $L_3%s%s$\\\\[3pt]",
                   it$meta$obj, it$meta$N, it$meta$M, it$meta$case, it$meta$value,
                   if (it$meta$mode=="eq") "=" else "\\le",
                   sprintf(paste0("%.", digits, "f"), it$meta$L3))
    writeLines(c("", "% ---", cap, sprintf("\\input{%s}", it$path), "\\medskip"), con, useBytes = TRUE)
  }
  message(sprintf("[tikz/master] %s", normalizePath(master_filename, mustWork = FALSE)))
  invisible(list(files = vapply(outs, function(x) x$path, ""), master = normalizePath(master_filename, mustWork = FALSE)))
}

#──────────────────────── 13. 実行セクション（固定） ─────────────#
# N=1000, M=100 固定、並列なし、進捗なし、split2N のみ
N <- 1000
M <- 100

L1_seq <- seq(0.90, 1.00, by = 0.025)
L2_seq <- seq(0.90, 1.00, by = 0.025)
L3_seq <- seq(0.90, 1.00, by = 0.025)

# シナリオは run_L123_sweep_simple 内で確定
# 分母インデックスを先に作成（目的関数に依存）
OBS_DENOM_IDX_LIST <- collect_obs_denom_indices(obj_specs, grid, m, n)

# 実行（逐次・単純化）
run_L123_sweep_simple(
  L1_seq = L1_seq, L2_seq = L2_seq, L3_seq = L3_seq,
  obj_specs = obj_specs, N = N, M = M
)

# 以降、export_* を必要に応じて呼んでください
# 例）export_tikz_heatmap_from_store(`0912Revised_RESULT_simulation_L1L2L3`, "P(Y0=0,Y1=0,Y2=1)", N, M, L3_val=0.95, case_for_values="both", value="mean_lb")










# ================= 出力（表のみ）完全版 =================
# 依存：dplyr が必要。未ロードなら次を有効化：
# library(dplyr)

# --- ユーティリティ（フォルダ作成・スラッグ化） ---
.ensure_dir <- function(path) dir.create(path, recursive = TRUE, showWarnings = FALSE)
.slugify <- function(x) {
  x <- gsub("\\s+", "-", x)
  x <- gsub("[^A-Za-z0-9._-]+", "-", x)
  x <- gsub("-+", "-", x)
  x <- gsub("(^-|-$)", "", x)
  tolower(x)
}

# --- ストアから summary を安全に取り出す ---
# --- ストアから summary を安全に取り出す（0912版のキーに合わせる） ---
get_summary_from_store <- function(store, obj_name, N, M) {
  ckey <- sprintf("Nexp=%d_Nobs=%d", as.integer(N), as.integer(N))
  mkey <- sprintf("M=%d", as.integer(M))
  stopifnot(is.list(store), obj_name %in% names(store))
  stopifnot(ckey %in% names(store[[obj_name]]))
  stopifnot(mkey %in% names(store[[obj_name]][[ckey]]))
  sumdf <- store[[obj_name]][[ckey]][[mkey]]$summary
  if (is.null(sumdf) || !is.data.frame(sumdf) || nrow(sumdf) == 0)
    stop("summary が見つからない / 空です: ", obj_name, " ", ckey, " ", mkey)
  sumdf
}

# --- 0831式「LBとUBを同じ表に」1枚出力（valueは無視） ---
export_table_from_store <- function(
    store, obj_name, N, M,
    L3_val,
    case_for_values = "both",
    value = c("mean_lb","mean_ub"),
    L_vals = NULL,
    L3_mode = c("eq","le"),
    digits = 3,
    out_dir = file.path("tex","L1L2L3")
){
  res <- export_lbub_grid_from_store(
    store = store, obj_name = obj_name, N = N, M = M,
    L3_val = L3_val, case_for_values = case_for_values,
    L_vals = L_vals,
    title_prefix = switch(case_for_values, exp="Exp.", obs="Obs.", both="Both", paste0("case=", case_for_values)),
    L3_mode = match.arg(L3_mode),
    digits = digits,
    out_dir = out_dir
  )
  invisible(res)
}


# --- コア：L1×L2 の LB/UB グリッドを LaTeX tabular で書き出す ---
export_lbub_grid_tabular <- function(
    df,                       # summary データフレーム（case/L1/L2/L3/mean_* 等を含む）
    L3_val,                   # 見出し用 L3 値
    case_for_values = "both", # "exp" | "obs" | "both"
    L_vals = NULL,            # 行・列の L1/L2 値。NULL=自動検出
    title_prefix = "Both",    # 見出しの左肩（"Exp." / "Obs." / "Both" など）
    L3_mode = c("eq","le"),   # "eq": L3一致 / "le": L3以下で最大
    digits = 3,               # 表示桁（0.900 など）
    out_dir = file.path("tex","L1L2L3"),
    file_stub = "lbub_grid",  # ファイル名の先頭
    extra_tags = NULL         # 追加タグ（obj/N/M など）
){
  stopifnot(is.data.frame(df))
  L3_mode <- match.arg(L3_mode)
  eps  <- 10^(-(digits+1))
  ffmt <- paste0("%.", digits, "f")
  fnum <- function(v) {
    v2 <- ifelse(is.na(v), NA_real_, ifelse(abs(v) < 0.5 * 10^(-digits), 0, v))
    ifelse(is.na(v2), "", sprintf(ffmt, v2))
  }
  
  # 1) 対象ケース抽出（_true を除外／無ければフォールバック）
  base <- df[df$case == case_for_values & !grepl("_true$", df$case), , drop = FALSE]
  if (nrow(base) == 0) {
    base <- df[df$case == paste0(case_for_values, "_true"), , drop = FALSE]
    base$case <- sub("_true$", "", base$case)
  }
  if (nrow(base) == 0) stop("指定 case の行が見つかりません: ", case_for_values)
  
  # 2) L3 フィルタ
  x <- base
  if (L3_mode == "eq") {
    x <- x[abs(x$L3 - L3_val) < eps, , drop = FALSE]
  } else {
    x <- x[x$L3 <= L3_val + eps, , drop = FALSE]
    if (nrow(x) > 0) {
      x <- x |>
        dplyr::group_by(L1, L2) |>
        dplyr::slice_max(L3, n = 1, with_ties = FALSE) |>
        dplyr::ungroup()
    }
  }
  
  # 3) L1/L2 並び
  if (is.null(L_vals)) {
    L1_vals <- sort(unique(round(base$L1, digits)))
    L2_vals <- sort(unique(round(base$L2, digits)))
  } else {
    L1_vals <- L_vals
    L2_vals <- L_vals
  }
  
  # 4) セル文字列（平均と 2.5/97.5% を "[lo, hi]" で）
  make_cell <- function(m, lo, hi) {
    if (is.na(m)) return("")
    paste0(fnum(m), " [", fnum(lo), ", ", fnum(hi), "]")
  }
  pick_row <- function(L1v, L2v) {
    row <- x[abs(x$L1 - L1v) < eps & abs(x$L2 - L2v) < eps, , drop = FALSE]
    if (nrow(row) == 0) return(list(lb="", ub=""))
    r <- row[1,]
    list(
      lb = make_cell(r$mean_lb, r$ci_lb_lo, r$ci_lb_hi),
      ub = make_cell(r$mean_ub, r$ci_ub_lo, r$ci_ub_hi)
    )
  }
  
  # 5) LaTeX 組み立て（図なし、tabular のみ）
  colspec <- paste0("cc|", paste(rep("c", length(L2_vals)), collapse="|"))
  header_title <- if (L3_mode == "eq") {
    paste0(title_prefix, " \\quad $L_3 = ", fnum(L3_val), "$")
  } else {
    paste0(title_prefix, " \\quad $L_3 \\le ", fnum(L3_val), "$")
  }
  col_heads <- paste(sprintf("$L_2 = %s$", fnum(L2_vals)), collapse = " & ")
  ncols <- 2 + length(L2_vals)
  title_line <- sprintf("\\multicolumn{%d}{c}{%s} \\\\", ncols, header_title)
  
  lines <- c()
  for (L1v in L1_vals) {
    lb_cells <- vapply(L2_vals, function(L2v) pick_row(L1v, L2v)$lb, "")
    lines <- c(lines, paste0("$L_1 = ", fnum(L1v), "$ & LB & ", paste(lb_cells, collapse = " & "), " \\\\"))
    ub_cells <- vapply(L2_vals, function(L2v) pick_row(L1v, L2v)$ub, "")
    lines <- c(lines, paste0("$L_1 = ", fnum(L1v), "$ & UB & ", paste(ub_cells, collapse = " & "), " \\\\"))
    lines <- c(lines, "    \\hline")
  }
  
  latex <- paste0(
    "\\begin{tabular}{", colspec, "}\n",
    "    ", title_line, "\n",
    "    \\hline\n",
    "    & & ", col_heads, " \\\\\n",
    "    \\hline\n",
    "    ", paste(lines, collapse = "\n    "), "\n",
    "    \\end{tabular}\n"
  )
  
  # 6) 書き出し
  .ensure_dir(out_dir)
  L3_tag <- gsub("\\.", "p", sprintf(ffmt, L3_val))
  tag <- paste(c(extra_tags, paste0("L3-", L3_tag), L3_mode, case_for_values), collapse = "_")
  fn <- file.path(out_dir, sprintf("%s_%s.tex", file_stub, tag))
  writeLines(latex, fn, useBytes = TRUE)
  
  invisible(list(path = normalizePath(fn, mustWork = FALSE),
                 label = paste0(title_prefix, " | case=", case_for_values,
                                " | L3=", sprintf(ffmt, L3_val),
                                " | mode=", L3_mode),
                 latex = latex))
}

# --- ラッパ：store から直接 1 枚出力 ---
export_lbub_grid_from_store <- function(
    store, obj_name, N, M,
    L3_val,
    case_for_values = "both",
    L_vals = NULL,
    title_prefix = NULL,   # NULL なら case から自動
    L3_mode = c("eq","le"),
    digits = 3,
    out_dir = file.path("tex","L1L2L3")
){
  df <- get_summary_from_store(store, obj_name, N, M)
  if (is.null(title_prefix)) {
    title_prefix <- switch(case_for_values,
                           exp = "Exp.", obs = "Obs.", both = "Both",
                           paste0("case=", case_for_values))
  }
  obj_slug <- .slugify(obj_name)
  file_stub <- paste0("lbub_grid_", obj_slug, "_N", N, "_M", M)
  export_lbub_grid_tabular(
    df = df,
    L3_val = L3_val,
    case_for_values = case_for_values,
    L_vals = L_vals,
    title_prefix = title_prefix,
    L3_mode = match.arg(L3_mode),
    digits = digits,
    out_dir = out_dir,
    file_stub = file_stub,
    extra_tags = NULL
  )
}

# --- 一括生成＋マスター .tex も書く ---
export_lbub_grids_and_master <- function(
    store,
    obj_names,           # 例：names(store)
    N_values,            # 例：c(1000)
    M_values,            # 例：c(100)
    L3_values,           # 例：c(0.90, 0.925, 0.95, 0.975, 1.00)
    cases = c("both"),   # 例：c("exp","obs","both")
    L_vals = NULL,       # 行列の L 値。NULL=自動
    L3_mode = "eq",
    digits = 3,
    out_dir = file.path("tex","L1L2L3"),
    master_filename = NULL
){
  .ensure_dir(out_dir)
  out_list <- list()
  
  for (obj in obj_names) {
    for (N in N_values) for (M in M_values) {
      for (cs in cases) {
        title_prefix <- switch(cs, exp="Exp.", obs="Obs.", both="Both", paste0("case=", cs))
        for (L3v in L3_values) {
          res <- export_lbub_grid_from_store(
            store = store, obj_name = obj, N = N, M = M,
            L3_val = L3v, case_for_values = cs,
            L_vals = L_vals, title_prefix = title_prefix,
            L3_mode = L3_mode, digits = digits, out_dir = out_dir
          )
          out_list[[length(out_list)+1]] <- c(
            res,
            meta = list(obj = obj, N = N, M = M, case = cs, L3 = L3v, mode = L3_mode)
          )
        }
      }
    }
  }
  
  # すべての表を \input で並べる “総まとめ .tex”
  if (is.null(master_filename)) {
    scope_tag <- paste0("N", paste(N_values, collapse="+"),
                        "_M", paste(M_values, collapse="+"),
                        "_", L3_mode)
    master_filename <- file.path(out_dir, paste0("lbub_all_", scope_tag, ".tex"))
  }
  con <- file(master_filename, open = "wb")
  on.exit(close(con), add = TRUE)
  
  writeLines("% === Auto-generated list of LB/UB grids ===", con, useBytes = TRUE)
  for (it in out_list) {
    line_title <- sprintf("\\noindent\\textbf{Objective: %s}\\\\ N=%d, M=%d, case=%s, $L_3=%s$, mode=%s\\\\[3pt]",
                          it$meta$obj, it$meta$N, it$meta$M, it$meta$case,
                          sprintf(paste0("%.", digits, "f"), it$meta$L3), it$meta$mode)
    rel <- it$path
    writeLines(c("", "% ---", line_title,
                 sprintf("\\input{%s}", rel),
                 "\\medskip"), con, useBytes = TRUE)
  }
  message(sprintf("[master] %s", normalizePath(master_filename, mustWork = FALSE)))
  
  invisible(list(files = vapply(out_list, function(x) x$path, ""),
                 master = normalizePath(master_filename, mustWork = FALSE)))
}


#### ================= 表出力（0912 版のみ・図なし・出力専用） ================= ####

# 出力先
out_dir <- file.path("tex","L1L2L3")
if (!dir.exists(out_dir)) dir.create(out_dir, recursive = TRUE, showWarnings = FALSE)

# データ元は 0912 版のみ（固定）
store <- `0912Revised_RESULT_simulation_L1L2L3`

# 出力対象（0831と同じノリで固定）
obj_set <- c("P(Y0=0,Y1=0,Y2=1)", "E[Y1-Y0 | X=2,Y=2]")  # 必要ならここだけ編集
Lset    <- c(0.90, 0.925, 0.95, 0.975, 1.00)
cases   <- c("exp","obs","both")
values  <- c("mean_lb","mean_ub")
N <- 1000
M <- 100
digits <- 3

# 個別の表をすべて出力（※ get_summary_from_store は直叩きしない）
outputs <- list()
for (obj in obj_set) {
  for (cs in cases) {
    for (vv in values) {
      for (L3v in Lset) {
        r <- export_table_from_store(
          store = store, obj_name = obj,
          N = N, M = M,
          L3_val = L3v,
          case_for_values = cs,
          value = vv,
          L_vals = Lset,   # 行・列の L はこのグリッドで固定
          L3_mode = "eq",  # L3 = 定数の面
          digits   = digits,
          out_dir  = out_dir
        )
        outputs[[length(outputs)+1]] <- list(
          path  = r$path,
          obj   = obj,
          case  = cs,
          value = vv,
          L3    = L3v
        )
      }
    }
  }
}

# master .tex を作成（\input を並べるだけ）
master_filename <- file.path(out_dir, sprintf("tables_all_N%d_M%d_eq.tex", N, M))
con <- file(master_filename, open = "wb"); on.exit(close(con), add = TRUE)
writeLines("% === 0912-style tables (tabular only) ===", con, useBytes = TRUE)
for (it in outputs) {
  cap <- sprintf("\\noindent\\textbf{Objective: %s}\\\\ N=%d, M=%d, case=%s, value=%s, $L_3=%s$\\\\[3pt]",
                 it$obj, N, M, it$case, it$value, sprintf(paste0("%.", digits, "f"), it$L3))
  writeLines(c("", "% ---", cap, sprintf("\\input{%s}", it$path), "\\medskip"), con, useBytes = TRUE)
}
close(con)
message(sprintf("[tables/master] %s", normalizePath(master_filename, mustWork = FALSE)))

#### ========================= ここまで（図は一切出さない） ========================= ####
