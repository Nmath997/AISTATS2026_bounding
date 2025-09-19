#──────────────────────── 0. ライブラリ ────────────────────────#
# install.packages(c("Matrix","Rglpk","dplyr","tidyr","e1071","purrr","tibble",
#                    "future","future.apply","progress"))
library(Matrix)
library(Rglpk)
library(dplyr)
library(tidyr)
library(e1071)
library(purrr)
library(tibble)
library(parallel)

library(future)
library(future.apply)
library(progress)


# 結果ルート（Rでは先頭数字名はバッククォートが必要）
`0909revised_RESULT_bounds` <- list()
RESULT_bounds_0909revised <- `0909revised_RESULT_bounds`  # 参照用エイリアス

# 共通サンプル・バンク（Exp/Obs を分離；Nごとに保持）
`0909revised_SAMPLING_BANK_EXP` <- list()  # list("Nexp=10" = list(samples=list(...)), ...)
SAMPLING_BANK_EXP_0909revised <- `0909revised_SAMPLING_BANK_EXP`  # 参照用
`0909revised_SAMPLING_BANK_OBS` <- list()  # list("Nobs=10" = list(samples=list(...)), ...)
SAMPLING_BANK_OBS_0909revised <- `0909revised_SAMPLING_BANK_OBS`  # 参照用



#──────────────────────── 1. 基本パラメータ ──────────────────#
m <- 3     # 潜在反応変数の本数 (Y1..Ym)
n <- 3     # 各 Y の水準数

#──────────────────────── 2. グリッド生成 ───────────────────#
Y_list <- setNames(lapply(seq_len(m), \(.) seq_len(n)), paste0("Y", seq_len(m)))
grid <- do.call(expand.grid, c(Y_list, list(X = seq_len(m)), list(Y = seq_len(n))))
Z <- nrow(grid)

# ケース名（順序もここで固定）
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

# ---- 疎行列でイベント制約（dense回避、空イベントも厳格化） ----
relation_blocks <- function(rel_mat, lb, ub, grid) {
  idx_all <- seq_len(nrow(grid))
  for (i in seq_len(nrow(rel_mat))) for (j in seq_len(ncol(rel_mat))) {
    rel <- rel_mat[i, j]; if (is.na(rel)) next
    idx_all <- intersect(idx_all, relation_idx(grid, i, j, rel))
  }
  Zloc <- nrow(grid)
  if (!length(idx_all)) {
    out <- list()
    if (!is.null(lb)) out$lb_event <- list(mat = Matrix(0, 1, Zloc, sparse = TRUE), dir = ">=", rhs = lb)
    if (!is.null(ub)) out$ub_event <- list(mat = Matrix(0, 1, Zloc, sparse = TRUE), dir = "<=", rhs = ub)
    return(out)
  }
  row1 <- sparseMatrix(i = rep(1L, length(idx_all)), j = as.integer(idx_all),
                       x = 1, dims = c(1L, Zloc))
  blocks <- list()
  if(!is.null(lb)) blocks$lb_event <- list(mat = row1, dir = ">=", rhs = lb)
  if(!is.null(ub)) blocks$ub_event <- list(mat = row1, dir = "<=", rhs = ub)
  blocks
}

compile_blocks <- function(blocks){
  mats <- lapply(blocks, `[[`, "mat")
  dirs <- lapply(blocks, `[[`, "dir")
  rhs  <- lapply(blocks, `[[`, "rhs")
  keep <- vapply(mats, function(M) !is.null(M) && nrow(M) > 0, logical(1))
  mats_kept <- mats[keep]
  mats_kept <- lapply(mats_kept, function(M) if (inherits(M, "dgCMatrix")) M else as(M, "dgCMatrix"))
  A <- if (length(mats_kept)) do.call(rbind, mats_kept) else Matrix(0,0,0, sparse=TRUE)
  dir <- unlist(dirs[keep], use.names = FALSE)
  rhs <- unlist(rhs[keep], use.names = FALSE)
  list(A=A, dir=dir, rhs=rhs)
}

`%||%` <- function(x, y) if (is.null(x)) y else x


marginal_mat <- function(idx_list, Z){
  rows <- rep(seq_along(idx_list), lengths(idx_list))
  cols <- unlist(idx_list)
  sparseMatrix(i = rows, j = cols, x = 1, dims = c(length(idx_list), Z))
}

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
  idx <- as.integer(idx); idx <- idx[is.finite(idx) & !is.na(idx)]
  Zloc <- nrow(grid); idx <- idx[idx >= 1L & idx <= Zloc]
  if (!length(idx)) return(list())
  row1 <- sparseMatrix(i = rep(1L, length(idx)), j = idx, x = 1, dims = c(1L, Zloc))
  out <- list()
  if (!is.null(lb)) out[["lb_event"]] <- list(mat = row1, dir = ">=", rhs = lb)
  if (!is.null(ub)) out[["ub_event"]] <- list(mat = row1, dir = "<=", rhs = ub)
  out
}

# ── 各目的関数の全 N をまとめた summary 表 ──
build_summary_allN <- function(obj_runs) {
  rows <- list()
  for (keyNexp in names(obj_runs)) {
    if (!grepl("^Nexp=", keyNexp)) next
    N_exp_val <- suppressWarnings(as.integer(sub("^Nexp=([0-9]+)$", "\\1", keyNexp)))
    node_exp  <- obj_runs[[keyNexp]]
    if (!is.list(node_exp)) next
    for (keyNobs in names(node_exp)) {
      if (!grepl("^Nobs=", keyNobs)) next
      N_obs_val <- suppressWarnings(as.integer(sub("^Nobs=([0-9]+)$", "\\1", keyNobs)))
      node_obs  <- node_exp[[keyNobs]]
      if (!is.list(node_obs)) next
      for (Mk in names(node_obs)) {
        if (!grepl("^M=", Mk)) next
        res <- node_obs[[Mk]]
        if (is.null(res) || is.null(res$summary)) next
        sm <- res$summary
        sm$N_exp <- N_exp_val
        sm$N_obs <- N_obs_val
        sm$N     <- if (!is.na(N_obs_val)) N_obs_val else N_exp_val  # 互換表示列
        sm$M     <- suppressWarnings(as.integer(sub("^M=([0-9]+)$", "\\1", Mk)))
        rows[[paste(keyNexp, keyNobs, Mk, sep=":")]] <- sm
      }
    }
  }
  if (!length(rows)) return(data.frame())
  df <- dplyr::bind_rows(rows)
  dplyr::arrange(df, N_exp, N_obs, M, scenario, case)
}


pb_tick_safe <- function(pb, tokens = NULL){
  if (is.null(pb)) return(invisible(NULL))
  # 既に終了していても落ちないように try で保護
  try(pb$tick(tokens = tokens), silent = TRUE)
  invisible(NULL)
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
    
    labels <- character()
    if (!is.null(obj_spec$target_eq)) {
      eq_idx <- which(!is.na(obj_spec$target_eq))
      labels <- c(labels, paste0("Y", eq_idx, "=", obj_spec$target_eq[eq_idx]))
    }
    if (!is.null(obj_spec$target_ineq)) {
      labels <- c(labels, vapply(obj_spec$target_ineq, function(c) paste0("Y",c$var,c$op,c$val), ""))
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
      eq_list <- lapply(eq_idx, function(i) list(var=i, op="==", val=obj_spec$target_eq[i]))
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
      labels <- c(labels, vapply(obj_spec$target_ineq, function(c) paste0("Y",c$var,c$op,c$val), ""))
    }
    base_label <- if(length(labels)>0) paste(labels, collapse=",") else "Y1…Ym"
    cond_label <- if(!is.null(obj_spec$condX) && !is.null(obj_spec$condY)) sprintf("|X=%d,Y=%d", obj_spec$condX, obj_spec$condY) else ""
    obj_label <- sprintf("P(%s%s)", base_label, cond_label)
    return(list(obj_vec=obj_vec, denom_lab=NULL, obj_label=obj_label))
  } else if (obj_spec$type == "order") {
    rel_mat <- obj_spec$rel_mat
    idx <- seq_len(Z)
    for (i in seq_len(nrow(rel_mat))) for (j in seq_len(ncol(rel_mat))) {
      rel <- rel_mat[i,j]; if (is.na(rel)) next
      idx <- intersect(idx, relation_idx(grid, i, j, rel))
    }
    obj_vec <- integer(Z); obj_vec[idx] <- 1
    terms <- which(!is.na(rel_mat), arr.ind=TRUE)
    label_terms <- apply(terms, 1, function(rc) paste0("Y", rc[1], rel_mat[rc[1], rc[2]], "Y", rc[2]))
    obj_label <- paste0("P(", paste(label_terms, collapse=" & "), ")")
    return(list(obj_vec=obj_vec, denom_lab=NULL, obj_label=obj_label))
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
    if (!is.null(obj_spec$condX) && !is.null(obj_spec$condY)) denom_lab <- sprintf("obs_k%d_y%d", obj_spec$condX, obj_spec$condY)
    else if (!is.null(obj_spec$condX)) denom_lab <- sprintf("obs_k%d_yALL", obj_spec$condX)
    else if (!is.null(obj_spec$condY)) denom_lab <- sprintf("obs_kALL_y%d", obj_spec$condY)
    label_cond <- ""
    if (!is.null(obj_spec$condX) || !is.null(obj_spec$condY)) {
      parts <- c()
      if (!is.null(obj_spec$condX)) parts <- c(parts, sprintf("X=%d", obj_spec$condX - 1))
      if (!is.null(obj_spec$condY)) parts <- c(parts, sprintf("Y=%d", obj_spec$condY - 1))
      label_cond <- paste0("|", paste(parts, collapse=","))
    }
    obj_label <- if (!is.null(obj_spec$label_override)) obj_spec$label_override else paste0("E[g(Y)", label_cond, "]")
    return(list(obj_vec=w_num, denom_lab=denom_lab, obj_label=obj_label))
  } else stop("unknown type")
}

# 例：目的関数
obj_specs <- list(
  "P(Y0=0,Y1=0,Y2=1)" = list(type="joint", target_eq=c(1,1,2), target_ineq=NULL, condX=NULL, condY=NULL),
  "E[Y1-Y0 | X=2,Y=2]" = list(
    type="linear", var_coefs=c(-1,1,0), intercept=0, zero_based=TRUE,
    condX=3, condY=3, label_override="E[Y1-Y0|X=2,Y=2]"
  ),
  "P(Y0=1,Y1=0,Y2=1,X=1,Y=0)" = list(
    type="joint", target_eq=c(2,1,2), target_ineq=NULL, condX=2, condY=1
  )
)

#──────────────────────── 5. シナリオ定義 ───────────────────#
idx_exp <- idx_obs <- vector("list", m*n)
cnt <- 1
for(k in seq_len(m)) for(y in seq_len(n)){
  idx_exp[[cnt]] <- which(grid[[paste0("Y",k)]] == y)
  idx_obs[[cnt]] <- which(grid$X==k & grid$Y==y)
  cnt <- cnt + 1
}
names(idx_exp) <- sprintf("exp_k%d_y%d", rep(seq_len(m), each=n), rep(seq_len(n), m))
names(idx_obs) <- sprintf("obs_k%d_y%d", rep(seq_len(m), each=n), rep(seq_len(n), m))
mat_exp <- marginal_mat(idx_exp, Z)
mat_obs <- marginal_mat(idx_obs, Z)

bad_rows <- consistency_bad(grid, m)
zero_mat <- function(idx, Z){
  if(length(idx)==0) return(NULL)
  sparseMatrix(i = seq_along(idx), j = idx, x = 1, dims = c(length(idx), Z))
}
base_blocks <- list(
  sum = list(mat = Matrix(1,1,Z,sparse=TRUE), dir = "==", rhs = 1),
  zero = list(mat = zero_mat(bad_rows, Z), dir = rep("==", length(bad_rows)), rhs = rep(0, length(bad_rows)))
)

# unused: 現状未使用（残す場合は今後の拡張用）
band_idx_pair <- function(grid, i, j, k) {
  Yi <- grid[[paste0("Y", i)]]
  Yj <- grid[[paste0("Y", j)]]
  which((Yi - Yj) >= 0 & (Yi - Yj) <= k)
}

{
  NAm <- matrix(NA_character_, nrow = m, ncol = m)
  tbl_none  <- NAm
  tbl_0Lq2  <- NAm; tbl_0Lq2[1,3] <- "<="
  tbl_0Lq1  <- NAm; tbl_0Lq1[1,2] <- "<="
  tbl_1Lq2  <- NAm; tbl_1Lq2[2,3] <- "<="
  tbl_chain <- NAm; tbl_chain[1,2] <- "<="; tbl_chain[2,3] <- "<="
  
  constraint_scenarios <- list()
  constraint_scenarios[["none"]]               <- list(rel_mat = tbl_none,  lb = NULL, ub = NULL)
  constraint_scenarios[["Y0<=Y1 a.s."]]        <- list(rel_mat = tbl_0Lq1, lb = 1,    ub = NULL)
  constraint_scenarios[["Y1<=Y2 a.s."]]        <- list(rel_mat = tbl_1Lq2, lb = 1,    ub = NULL)
  constraint_scenarios[["Y0<=Y1<=Y2 a.s."]]    <- list(rel_mat = tbl_chain, lb = 1,   ub = NULL)
}

#──────────────────────── 6. PO分布の構築（Appendix C.1 型） ──────────#
a_xy <- matrix(c(
  0.15, 0.1, 0.1,
  0.1,  0.2, 0.1,
  0.05, 0.1, 0.1
), nrow = m, ncol = n, byrow = TRUE)
a_xy <- a_xy / sum(a_xy)

# 真値に単調性を課すか（既定 TRUE）
enforce_monotone_true <- TRUE
good_idx <- {
  base_ok <- setdiff(seq_len(nrow(grid)), consistency_bad(grid, m))
  if (enforce_monotone_true) intersect(base_ok, monotone_idx(grid, m)) else base_ok
}
denom_xy <- table(factor(grid$X[good_idx], levels = seq_len(m)),
                  factor(grid$Y[good_idx], levels = seq_len(n)))
denom_xy <- as.matrix(denom_xy)
if (any(denom_xy == 0)) stop("Some (x,y) cells have zero admissible configs under monotonicity+consistency.")

po_prob <- numeric(Z)
ix <- good_idx
po_prob[ix] <- a_xy[cbind(grid$X[ix], grid$Y[ix])] / denom_xy[cbind(grid$X[ix], grid$Y[ix])]
stopifnot(abs(sum(po_prob) - 1) < 1e-12)

pxy_mat <- tapply(po_prob, list(grid$X, grid$Y), sum)
pXY     <- as.vector(t(pxy_mat))
pY_list <- lapply(seq_len(m), function(k) as.numeric(tapply(po_prob, grid[[paste0("Y", k)]], sum)))

#──────────────────────── 7. LP ラッパ（安全版） ─────────────────────#
run_lp_safe <- function(obj, A, dir, rhs, maximise = FALSE) {
  ctrl1 <- list(canonicalize_status=TRUE, presolve=TRUE,  verbose=FALSE, tm_limit=0)
  ctrl2 <- list(canonicalize_status=TRUE, presolve=FALSE, verbose=FALSE, tm_limit=0)
  bounds <- list(lower = list(ind = seq_len(length(obj)), val = rep(0, length(obj))),
                 upper = list(ind = seq_len(length(obj)), val = rep(1, length(obj))))
  .solve <- function(ctrl) Rglpk::Rglpk_solve_LP(obj=obj, mat=A, dir=dir, rhs=rhs, bounds=bounds, max=maximise, control=ctrl)
  sol <- .solve(ctrl1); if (!is.null(sol$status) && sol$status == 0) return(sol)
  sol2 <- .solve(ctrl2); if (!is.null(sol2$status) && sol2$status == 0) return(sol2)
  sol2
}

#──────────────────────── 8. 最適化（ケース別） ──────────────────────#
run_for_obj <- function(obj_spec, spec_name){
  obj <- make_obj(obj_spec, grid)
  result_tbl <- data.frame(
    scenario   = character(), case=character(),
    min_val    = numeric(),   max_val    = numeric(),
    min_status = integer(),   max_status = integer(),
    li_lb      = numeric(),   li_ub      = numeric(),
    stringsAsFactors = FALSE
  )
  sol_list <- list()
  
  has_exp <- exists("pY_list") && is.list(pY_list) && length(pY_list)==m
  has_obs <- exists("pXY")     && is.numeric(pXY)  && length(pXY)==m*n
  
  cases <- character()
  if (has_exp)             cases <- c(cases, "exp")
  if (has_obs)             cases <- c(cases, "obs")
  if (has_exp && has_obs)  cases <- c(cases, "both")
  
  if (has_exp) { b_exp <- unlist(pY_list); names(b_exp) <- names(idx_exp); mat_exp <- marginal_mat(idx_exp, Z) }
  if (has_obs) { b_obs <- pXY;             names(b_obs) <- names(idx_obs); mat_obs <- marginal_mat(idx_obs, Z) }
  
  get_pX_from_vec <- function(pXY_vec, m, n) { if (is.null(pXY_vec) || length(pXY_vec) != m*n) return(NULL); tapply(pXY_vec, rep(seq_len(m), each = n), sum) }
  get_pY_from_vec <- function(pXY_vec, m, n) { if (is.null(pXY_vec) || length(pXY_vec) != m*n) return(NULL); tapply(pXY_vec, rep(seq_len(n), times = m), sum) }
  pX <- if (has_obs) get_pX_from_vec(if (exists("b_obs")) b_obs else pXY, m, n) else NULL
  if (!is.null(pX)) names(pX) <- sprintf("obs_k%d_yALL", seq_len(m))
  pY <- if (has_obs) get_pY_from_vec(if (exists("b_obs")) b_obs else pXY, m, n) else NULL
  if (!is.null(pY)) names(pY) <- sprintf("obs_kALL_y%d", seq_len(n))
  
  for (sname in names(constraint_scenarios)) {
    sc <- constraint_scenarios[[sname]]
    rel_blks_base <- list()
    if (!is.null(sc$rel_mat))  rel_blks_base <- relation_blocks(sc$rel_mat, sc$lb, sc$ub, grid)
    if (!is.null(sc$rel_list)) rel_blks_base <- c(rel_blks_base, do.call(c, lapply(sc$rel_list, \(info) relation_blocks(info$mat, info$lb, info$ub, grid))))
    if (!is.null(sc$idx))      rel_blks_base <- c(rel_blks_base, event_blocks_from_idx(sc$idx, sc$lb, sc$ub, grid))
    if (!is.null(sc$idx_list)) for (info in sc$idx_list) rel_blks_base <- c(rel_blks_base, event_blocks_from_idx(info$idx, info$lb, info$ub, grid))
    apply_to <- if (is.null(sc$apply_to)) c("exp","obs","both") else sc$apply_to
    
    for (cname in cases) {
      if (!(cname %in% apply_to)) {
        result_tbl <- rbind(result_tbl, data.frame(
          scenario=sname, case=cname,
          min_val=NA_real_, max_val=NA_real_,
          min_status=NA_integer_, max_status=NA_integer_,
          li_lb=NA_real_, li_ub=NA_real_, stringsAsFactors=FALSE
        ))
        next
      }
      add <- switch(cname,
                    exp  = list(mat=mat_exp, dir=rep("==",nrow(mat_exp)), rhs=b_exp),
                    obs  = list(mat=mat_obs, dir=rep("==",nrow(mat_obs)), rhs=b_obs),
                    both = list(mat=rbind(mat_exp,mat_obs),
                                dir=rep("==", nrow(mat_exp)+nrow(mat_obs)),
                                rhs=c(b_exp,b_obs))
      )
      rel_blks <- c(list(), rel_blks_base)
      if (!is.null(sc$band_k)) {
        idx_band <- band_idx(grid, m, sc$band_k)
        rel_blks <- c(rel_blks, event_blocks_from_idx(idx_band, lb=1, ub=NULL, grid))
      }
      
      blocks_to_compile <- c(base_blocks, rel_blks, list(marg=add))
      cmp <- compile_blocks(blocks_to_compile)
      sol_min <- run_lp_safe(obj$obj_vec, cmp$A, cmp$dir, cmp$rhs, FALSE)
      sol_max <- run_lp_safe(obj$obj_vec, cmp$A, cmp$dir, cmp$rhs, TRUE)
      
      denom <- 1
      if (!is.null(obj$denom_lab)) {
        if (exists("b_obs") && obj$denom_lab %in% names(b_obs))      denom <- b_obs[obj$denom_lab]
        else if (!is.null(pX) && obj$denom_lab %in% names(pX))       denom <- pX[[obj$denom_lab]]
        else if (!is.null(pY) && obj$denom_lab %in% names(pY))       denom <- pY[[obj$denom_lab]]
        else denom <- NA_real_
      }
      if (!is.null(obj$denom_lab) && cname == "exp") {
        res_min <- NA_real_; res_max <- NA_real_
      } else if (!is.null(obj$denom_lab)) {
        if (is.na(denom) || denom <= 0) { res_min <- NA_real_; res_max <- NA_real_ }
        else { res_min <- sol_min$optimum / denom; res_max <- sol_max$optimum / denom }
      } else { res_min <- sol_min$optimum; res_max <- sol_max$optimum }
      
      li_bounds <- c(lb = NA_real_, ub = NA_real_)
      if (sname == "none" && cname == "both" && (obj_spec$type %in% c("joint", "conditional"))) {
        li <- compute_lipearl_bounds_for_obj(obj_spec)
        if (!is.null(li)) {
          if (is.list(li) && !is.null(li$lb) && !is.null(li$ub)) { li_bounds["lb"] <- as.numeric(li$lb); li_bounds["ub"] <- as.numeric(li$ub) }
          else if (length(li) >= 2) { li_bounds["lb"] <- as.numeric(li[[1]]); li_bounds["ub"] <- as.numeric(li[[2]]) }
        }
      }
      
      result_tbl <- rbind(result_tbl, data.frame(
        scenario=sname, case=cname, min_val=res_min, max_val=res_max,
        min_status=sol_min$status, max_status=sol_max$status,
        li_lb=unname(li_bounds["lb"]), li_ub=unname(li_bounds["ub"]),
        stringsAsFactors = FALSE
      ))
      key_min <- paste(spec_name, sname, cname, "min", sep = "_")
      key_max <- paste(spec_name, sname, cname, "max", sep = "_")
      sol_list[[key_min]] <- sol_min$solution
      sol_list[[key_max]] <- sol_max$solution
    }
  }
  if (any(result_tbl$min_status != 0 | result_tbl$max_status != 0, na.rm = TRUE)) {
    message("[warn] 非最適(status!=0)の解が含まれます。件数: ",
            sum(result_tbl$min_status != 0 | result_tbl$max_status != 0, na.rm = TRUE))
  }
  list(results = result_tbl, solutions = sol_list, label = obj$obj_label)
}

split_replicates <- function(rep_df) {
  scenario_levels <- names(constraint_scenarios)
  scenario_levels <- scenario_levels[scenario_levels %in% rep_df$scenario]
  case_levels <- CASE_LEVELS[1:3]
  rep_df <- rep_df |>
    dplyr::mutate(scenario = factor(scenario, levels = scenario_levels),
                  case     = factor(case,     levels = case_levels))
  by_scn <- split(rep_df, rep_df$scenario); by_scn <- by_scn[scenario_levels]
  lapply(by_scn, function(df_s) {
    by_case <- split(df_s, df_s$case); by_case <- by_case[case_levels]
    lapply(by_case, function(x) {
      if (nrow(x) == 0) return(as.data.frame(x))
      cols <- c("rep", "min_val", "max_val")
      li_cols <- intersect(c("li_lb","li_ub"), names(x))
      cols <- unique(c(cols, li_cols))
      y <- x[, cols, drop = FALSE]; rownames(y) <- NULL; as.data.frame(y)
    })
  })
}

# ────────────────────── Feasible 判定（目的関数に依存しない） ──────────────────────
is_sample_feasible <- function(b_exp, b_obs) {
  has_exp <- !is.null(b_exp)
  has_obs <- !is.null(b_obs)
  cases <- character()
  if (has_exp)            cases <- c(cases, "exp")
  if (has_obs)            cases <- c(cases, "obs")
  if (has_exp && has_obs) cases <- c(cases, "both")
  if (!length(cases)) return(FALSE)
  
  for (sname in names(constraint_scenarios)) {
    sc <- constraint_scenarios[[sname]]
    rel_blks_base <- list()
    if (!is.null(sc$rel_mat))  rel_blks_base <- relation_blocks(sc$rel_mat, sc$lb, sc$ub, grid)
    if (!is.null(sc$rel_list)) rel_blks_base <- c(rel_blks_base, do.call(c, lapply(sc$rel_list, \(info) relation_blocks(info$mat, info$lb, info$ub, grid))))
    if (!is.null(sc$idx))      rel_blks_base <- c(rel_blks_base, event_blocks_from_idx(sc$idx, sc$lb, sc$ub, grid))
    if (!is.null(sc$idx_list)) for (info in sc$idx_list) rel_blks_base <- c(rel_blks_base, event_blocks_from_idx(info$idx, info$lb, info$ub, grid))
    
    apply_to <- if (is.null(sc$apply_to)) c("exp","obs","both") else sc$apply_to
    for (cname in cases) {
      if (!(cname %in% apply_to)) next
      add <- switch(cname,
                    exp  = list(mat = mat_exp, dir = rep("==", nrow(mat_exp)), rhs = b_exp),
                    obs  = list(mat = mat_obs, dir = rep("==", nrow(mat_obs)), rhs = b_obs),
                    both = list(mat = rbind(mat_exp, mat_obs),
                                dir = rep("==", nrow(mat_exp) + nrow(mat_obs)),
                                rhs = c(b_exp, b_obs))
      )
      rel_blks <- c(list(), rel_blks_base)
      if (!is.null(sc$band_k)) {
        idx_band <- band_idx(grid, m, sc$band_k)
        rel_blks <- c(rel_blks, event_blocks_from_idx(idx_band, lb=1, ub=NULL, grid))
      }
      cmp <- compile_blocks(c(base_blocks, rel_blks, list(marg = add)))
      obj0 <- numeric(ncol(cmp$A))
      sol  <- run_lp_safe(obj0, cmp$A, cmp$dir, cmp$rhs, maximise = FALSE)
      if (is.null(sol$status) || sol$status != 0) return(FALSE)
    }
  }
  TRUE
}

# ────────────────────── Feasible 判定（Exp/Obs 個別版） ──────────────────────
is_sample_feasible_exp <- function(b_exp) {
  if (is.null(b_exp)) return(FALSE)
  for (sname in names(constraint_scenarios)) {
    sc <- constraint_scenarios[[sname]]
    apply_to <- if (is.null(sc$apply_to)) c("exp","obs","both") else sc$apply_to
    if (!("exp" %in% apply_to)) next
    rel_blks_base <- list()
    if (!is.null(sc$rel_mat))  rel_blks_base <- relation_blocks(sc$rel_mat, sc$lb, sc$ub, grid)
    if (!is.null(sc$rel_list)) rel_blks_base <- c(rel_blks_base, do.call(c, lapply(sc$rel_list, \(info) relation_blocks(info$mat, info$lb, info$ub, grid))))
    if (!is.null(sc$idx))      rel_blks_base <- c(rel_blks_base, event_blocks_from_idx(sc$idx, sc$lb, sc$ub, grid))
    if (!is.null(sc$idx_list)) for (info in sc$idx_list) rel_blks_base <- c(rel_blks_base, event_blocks_from_idx(info$idx, info$lb, info$ub, grid))
    rel_blks <- c(list(), rel_blks_base)
    if (!is.null(sc$band_k)) {
      idx_band <- band_idx(grid, m, sc$band_k)
      rel_blks <- c(rel_blks, event_blocks_from_idx(idx_band, lb=1, ub=NULL, grid))
    }
    add <- list(mat = mat_exp, dir = rep("==", nrow(mat_exp)), rhs = b_exp)
    cmp <- compile_blocks(c(base_blocks, rel_blks, list(marg = add)))
    sol <- run_lp_safe(numeric(ncol(cmp$A)), cmp$A, cmp$dir, cmp$rhs, maximise = FALSE)
    if (is.null(sol$status) || sol$status != 0) return(FALSE)
  }
  TRUE
}

is_sample_feasible_obs <- function(b_obs) {
  if (is.null(b_obs)) return(FALSE)
  for (sname in names(constraint_scenarios)) {
    sc <- constraint_scenarios[[sname]]
    apply_to <- if (is.null(sc$apply_to)) c("exp","obs","both") else sc$apply_to
    if (!("obs" %in% apply_to)) next
    rel_blks_base <- list()
    if (!is.null(sc$rel_mat))  rel_blks_base <- relation_blocks(sc$rel_mat, sc$lb, sc$ub, grid)
    if (!is.null(sc$rel_list)) rel_blks_base <- c(rel_blks_base, do.call(c, lapply(sc$rel_list, \(info) relation_blocks(info$mat, info$lb, info$ub, grid))))
    if (!is.null(sc$idx))      rel_blks_base <- c(rel_blks_base, event_blocks_from_idx(sc$idx, sc$lb, sc$ub, grid))
    if (!is.null(sc$idx_list)) for (info in sc$idx_list) rel_blks_base <- c(rel_blks_base, event_blocks_from_idx(info$idx, info$lb, info$ub, grid))
    rel_blks <- c(list(), rel_blks_base)
    if (!is.null(sc$band_k)) {
      idx_band <- band_idx(grid, m, sc$band_k)
      rel_blks <- c(rel_blks, event_blocks_from_idx(idx_band, lb=1, ub=NULL, grid))
    }
    add <- list(mat = mat_obs, dir = rep("==", nrow(mat_obs)), rhs = b_obs)
    cmp <- compile_blocks(c(base_blocks, rel_blks, list(marg = add)))
    sol <- run_lp_safe(numeric(ncol(cmp$A)), cmp$A, cmp$dir, cmp$rhs, maximise = FALSE)
    if (is.null(sol$status) || sol$status != 0) return(FALSE)
  }
  TRUE
}

# ────────────────────── Feasible 判定（Both=Exp+Obs の同時充足） ──────────────────────
is_sample_feasible_both <- function(b_exp, b_obs) {
  if (is.null(b_exp) || is.null(b_obs)) return(FALSE)
  for (sname in names(constraint_scenarios)) {
    sc <- constraint_scenarios[[sname]]
    apply_to <- if (is.null(sc$apply_to)) c("exp","obs","both") else sc$apply_to
    if (!("both" %in% apply_to)) next
    rel_blks_base <- list()
    if (!is.null(sc$rel_mat))  rel_blks_base <- relation_blocks(sc$rel_mat, sc$lb, sc$ub, grid)
    if (!is.null(sc$rel_list)) rel_blks_base <- c(rel_blks_base, do.call(c, lapply(sc$rel_list, \(info) relation_blocks(info$mat, info$lb, info$ub, grid))))
    if (!is.null(sc$idx))      rel_blks_base <- c(rel_blks_base, event_blocks_from_idx(sc$idx, sc$lb, sc$ub, grid))
    if (!is.null(sc$idx_list)) for (info in sc$idx_list) rel_blks_base <- c(rel_blks_base, event_blocks_from_idx(info$idx, info$lb, info$ub, grid))
    rel_blks <- c(list(), rel_blks_base)
    if (!is.null(sc$band_k)) {
      idx_band <- band_idx(grid, m, sc$band_k)
      rel_blks <- c(rel_blks, event_blocks_from_idx(idx_band, lb=1, ub=NULL, grid))
    }
    add <- list(
      mat = rbind(mat_exp, mat_obs),
      dir = rep("==", nrow(mat_exp) + nrow(mat_obs)),
      rhs = c(b_exp, b_obs)
    )
    cmp <- compile_blocks(c(base_blocks, rel_blks, list(marg = add)))
    sol <- run_lp_safe(numeric(ncol(cmp$A)), cmp$A, cmp$dir, cmp$rhs, maximise = FALSE)
    if (is.null(sol$status) || sol$status != 0) return(FALSE)
  }
  TRUE
}

# 呼び名のズレ対策（ペア feasibility チェックの本体は is_sample_feasible_both）
is_pair_feasible_both <- function(b_exp, b_obs) {
  is_sample_feasible_both(b_exp, b_obs)
}


# ────────────────────── Both 可 feasibility ペアを M 個作る ──────────────────────
# 必要なら片側/両側のバンクを 1 本ずつ増やしながら探索します（重複は避ける方針）
ensure_feasible_pairs <- function(N_exp, N_obs, M, workers = 1, pb = NULL) {
  keyE <- .bank_key_exp(as.integer(N_exp))
  keyO <- .bank_key_obs(as.integer(N_obs))
  bankE <- `0909revised_SAMPLING_BANK_EXP`[[keyE]]; bankO <- `0909revised_SAMPLING_BANK_OBS`[[keyO]]
  if (is.null(bankE)) bankE <- ensure_sampling_bank_exp(Nexp = as.integer(N_exp), M = as.integer(M), workers = workers, pb = pb)
  if (is.null(bankO)) bankO <- ensure_sampling_bank_obs(Nobs = as.integer(N_obs), M = as.integer(M), workers = workers, pb = pb)
  
  # 重複使用は原則避ける：使い切ったら 1 本ずつ追加生成
  usedE <- rep(FALSE, length(bankE$samples))
  usedO <- rep(FALSE, length(bankO$samples))
  
  pairs <- vector("list", 0L)
  grow_guard <- 0L
  
  while (length(pairs) < as.integer(M)) {
    found <- FALSE
    # 探索：まだ使っていない組合せで feasible な (e,o) を探す
    for (ie in which(!usedE)) {
      # b_exp の作成（名前も付与）
      pY_list_i <- bankE$samples[[ie]]$pY_list
      b_exp_i   <- unlist(pY_list_i); names(b_exp_i) <- names(idx_exp)
      
      for (io in which(!usedO)) {
        b_obs_i <- bankO$samples[[io]]$pXY; names(b_obs_i) <- names(idx_obs)
        if (is_pair_feasible_both(b_exp_i, b_obs_i)) {
          pairs[[length(pairs) + 1L]] <- list(ie = ie, io = io)
          usedE[ie] <- TRUE; usedO[io] <- TRUE
          found <- TRUE
          break
        }
      }
      if (found) break
    }
    
    if (!found) {
      # どちらか（交互）を 1 本ずつ増やして探索空間を広げる
      grow_guard <- grow_guard + 1L
      needE <- sum(!usedE) < (as.integer(M) - length(pairs))
      needO <- sum(!usedO) < (as.integer(M) - length(pairs))
      
      if (!needE && !needO) { needE <- TRUE; needO <- TRUE }  # 探索停滞時は両側増やす
      
      if (needE) {
        haveE <- length(bankE$samples)
        bankE <- ensure_sampling_bank_exp(Nexp = as.integer(N_exp), M = haveE + 1L, workers = workers, pb = pb)
        usedE <- c(usedE, FALSE)
      }
      if (needO) {
        haveO <- length(bankO$samples)
        bankO <- ensure_sampling_bank_obs(Nobs = as.integer(N_obs), M = haveO + 1L, workers = workers, pb = pb)
        usedO <- c(usedO, FALSE)
      }
      
      # 無限ループ安全弁（現実的には到達しない想定）
      if (grow_guard > 10000L) stop("ensure_feasible_pairs(): too many attempts; check constraints.")
    }
  }
  
  list(pairs = pairs, bankE = bankE, bankO = bankO)
}



# ────────────────────── サンプリング・バンク（Exp/Obs を分離） ──────────────────────
.bank_key_exp <- function(Nexp) sprintf("Nexp=%d", as.integer(Nexp))
.bank_key_obs <- function(Nobs) sprintf("Nobs=%d", as.integer(Nobs))

get_sampling_bank_exp <- function(Nexp) { `0909revised_SAMPLING_BANK_EXP`[[.bank_key_exp(Nexp)]] }
get_sampling_bank_obs <- function(Nobs) { `0909revised_SAMPLING_BANK_OBS`[[.bank_key_obs(Nobs)]] }

ensure_sampling_bank_exp <- function(Nexp, M, workers = 1, pb = NULL) {
  key  <- .bank_key_exp(as.integer(Nexp))
  bank <- `0909revised_SAMPLING_BANK_EXP`[[key]]
  have <- if (!is.null(bank)) length(bank$samples) else 0L
  need <- max(0L, as.integer(M) - have)
  if (need == 0L) {
    cat(sprintf("[sampling:exp] reuse bank %s: have=%d need=%d\n", key, have, as.integer(M)))
    return(bank)
  }
  cat(sprintf("[sampling:exp] start Nexp=%d | need=%d (have=%d)\n", as.integer(Nexp), need, have))
  Zloc <- Z
  samples_new <- vector("list", need)
  
  gen_one <- function() {
    tries <- 0L
    repeat {
      tries <- tries + 1L
      idx <- sample.int(Zloc, size = as.integer(Nexp), replace = TRUE, prob = po_prob)
      pY_list_i <- lapply(seq_len(m), function(k) {
        yk <- grid[[paste0("Y", k)]][idx]
        as.numeric(table(factor(yk, levels = seq_len(n)))) / as.integer(Nexp)
      })
      b_exp_i <- unlist(pY_list_i); names(b_exp_i) <- names(idx_exp)
      if (is_sample_feasible_exp(b_exp_i)) {
        return(list(pY_list = pY_list_i, tries = tries))
      }
    }
  }
  
  if (workers > 1) {
    samples_new <- future.apply::future_lapply(
      seq_len(need), function(r) gen_one(),
      future.seed = TRUE, future.stdout = NA
    )
    # ←← ここで “各本数” に対して tick
    for (i in seq_len(need)) pb_tick_safe(pb, tokens = list(
      phase="sampling-exp", obj="-",
      Nexp=as.integer(Nexp), Nobs=NA_integer_,
      r=have+i, M=as.integer(M),
      tries=samples_new[[i]]$tries,
      sumtries=sum(vapply(samples_new[seq_len(i)], function(s) s$tries, integer(1)))
    ))
  } else {
    sumtries <- 0L
    for (r in seq_len(need)) {
      s <- gen_one()
      sumtries <- sumtries + s$tries
      samples_new[[r]] <- s
      # ←← 逐次でも同様に tick
      pb_tick_safe(pb, tokens = list(
        phase="sampling-exp", obj="-",
        Nexp=as.integer(Nexp), Nobs=NA_integer_,
        r=have+r, M=as.integer(M),
        tries=s$tries, sumtries=sumtries
      ))
    }
  }
  all_samples <- if (have > 0L) c(bank$samples, samples_new) else samples_new
  bank <- list(samples = all_samples)
  `0909revised_SAMPLING_BANK_EXP`[[key]] <<- bank
  SAMPLING_BANK_EXP_0909revised <<- `0909revised_SAMPLING_BANK_EXP`
  cat(sprintf("[sampling:exp] done Nexp=%d | bank %d -> %d\n", as.integer(Nexp), have, length(all_samples)))
  bank
}


ensure_sampling_bank_obs <- function(Nobs, M, workers = 1, pb = NULL) {
  key  <- .bank_key_obs(as.integer(Nobs))
  bank <- `0909revised_SAMPLING_BANK_OBS`[[key]]
  have <- if (!is.null(bank)) length(bank$samples) else 0L
  need <- max(0L, as.integer(M) - have)
  if (need == 0L) {
    cat(sprintf("[sampling:obs] reuse bank %s: have=%d need=%d\n", key, have, as.integer(M)))
    return(bank)
  }
  cat(sprintf("[sampling:obs] start Nobs=%d | need=%d (have=%d)\n", as.integer(Nobs), need, have))
  Zloc <- Z
  samples_new <- vector("list", need)
  
  gen_one <- function() {
    tries <- 0L
    repeat {
      tries <- tries + 1L
      idx <- sample.int(Zloc, size = as.integer(Nobs), replace = TRUE, prob = po_prob)
      tab_xy <- table(factor(grid$X[idx], levels = seq_len(m)), factor(grid$Y[idx], levels = seq_len(n)))
      pXY_i  <- as.vector(t(tab_xy)) / as.integer(Nobs)
      b_obs_i <- pXY_i; names(b_obs_i) <- names(idx_obs)
      if (is_sample_feasible_obs(b_obs_i)) {
        return(list(pXY = pXY_i, tries = tries))
      }
    }
  }
  
  if (workers > 1) {
    samples_new <- future.apply::future_lapply(
      seq_len(need), function(r) gen_one(),
      future.seed = TRUE, future.stdout = NA
    )
    # ←← 並列分
    for (i in seq_len(need)) pb_tick_safe(pb, tokens = list(
      phase="sampling-obs", obj="-",
      Nexp=NA_integer_, Nobs=as.integer(Nobs),
      r=have+i, M=as.integer(M),
      tries=samples_new[[i]]$tries,
      sumtries=sum(vapply(samples_new[seq_len(i)], function(s) s$tries, integer(1)))
    ))
  } else {
    sumtries <- 0L
    for (r in seq_len(need)) {
      s <- gen_one()
      sumtries <- sumtries + s$tries
      samples_new[[r]] <- s
      # ←← 逐次分
      pb_tick_safe(pb, tokens = list(
        phase="sampling-obs", obj="-",
        Nexp=NA_integer_, Nobs=as.integer(Nobs),
        r=have+r, M=as.integer(M),
        tries=s$tries, sumtries=sumtries
      ))
    }
  }
  all_samples <- if (have > 0L) c(bank$samples, samples_new) else samples_new
  bank <- list(samples = all_samples)
  `0909revised_SAMPLING_BANK_OBS`[[key]] <<- bank
  SAMPLING_BANK_OBS_0909revised <<- `0909revised_SAMPLING_BANK_OBS`
  cat(sprintf("[sampling:obs] done Nobs=%d | bank %d -> %d\n", as.integer(Nobs), have, length(all_samples)))
  bank
}



#──────────────────────── 8.5 シミュレーション ──────────────────────#
safe_mean <- function(x) if (all(is.na(x))) NA_real_ else mean(x, na.rm = TRUE)
safe_q    <- function(x, p) if (all(is.na(x))) NA_real_ else as.numeric(stats::quantile(x, probs = p, na.rm = TRUE, names = FALSE))

simulate_many <- function(obj_name, obj_spec, N_exp, N_obs, M, pb = NULL) {
  cat(sprintf("[opt] %s | N_exp=%d | N_obs=%d | M=%d\n",
              as.character(obj_name), as.integer(N_exp), as.integer(N_obs), as.integer(M)))
  
  pair_info <- ensure_feasible_pairs(
    N_exp = as.integer(N_exp),
    N_obs = as.integer(N_obs),
    M = as.integer(M),
    workers = 1,
    pb = NULL            # ← ここを NULL に
  )
  
  bankE <- pair_info$bankE; bankO <- pair_info$bankO
  pairs <- pair_info$pairs
  
  rep_list <- vector("list", as.integer(M))
  cum_tries <- 0L
  for (r in seq_len(as.integer(M))) {
    ie <- pairs[[r]]$ie; io <- pairs[[r]]$io
    pY_list <<- bankE$samples[[ie]]$pY_list
    pXY     <<- bankO$samples[[io]]$pXY
    
    tries_r <- (bankE$samples[[ie]]$tries %||% 0L) + (bankO$samples[[io]]$tries %||% 0L)
    cum_tries <- cum_tries + tries_r
    
    out <- run_for_obj(obj_spec, obj_name)
    tmp <- out$results |>
      dplyr::mutate(
        feasible = (min_status == 0 & max_status == 0),
        feasible = dplyr::coalesce(feasible, FALSE),
        min_val  = ifelse(feasible, min_val, NA_real_),
        max_val  = ifelse(feasible, max_val, NA_real_)
      ) |>
      dplyr::select(scenario, case, feasible, min_val, max_val, dplyr::any_of(c("li_lb","li_ub"))) |>
      dplyr::mutate(rep = r, tries = tries_r,
                    N_exp = as.integer(N_exp), N_obs = as.integer(N_obs))
    rep_list[[r]] <- tmp
    
    if (!is.null(pb)) pb_tick_safe(pb, tokens = list(
      phase="opt", obj=as.character(obj_name),
      Nexp=as.integer(N_exp), Nobs=as.integer(N_obs),
      r=as.integer(r), M=as.integer(M),
      tries=as.integer(tries_r), sumtries=as.integer(cum_tries)
    ))
    
  }
  
  rep_df <- dplyr::bind_rows(rep_list)
  has_li <- all(c("li_lb","li_ub") %in% names(rep_df))
  if (has_li) {
    base_both_none <- dplyr::filter(rep_df, scenario == "none", case == "both")
    if (nrow(base_both_none) > 0) {
      pseudo_li <- base_both_none |>
        dplyr::transmute(scenario = "Li–Pearl", case = "both",
                         min_val = li_lb, max_val = li_ub, rep, tries, N_exp, N_obs)
      rep_df <- dplyr::bind_rows(rep_df, pseudo_li)
    }
  }
  
  scenario_order <- c("Li–Pearl", names(constraint_scenarios))
  summary_df <- rep_df |>
    dplyr::mutate(scenario = factor(scenario, levels = scenario_order),
                  case     = factor(case,     levels = CASE_LEVELS[1:3])) |>
    dplyr::group_by(scenario, case, N_exp, N_obs) |>
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
      median_tries = safe_q(na.omit(tries), 0.5),
      .groups = "drop"
    )
  
  # 真値（維持）
  pXY_true <- as.vector(t(tapply(po_prob, list(grid$X, grid$Y), sum)))
  pY_list_true <- lapply(seq_len(m), function(k)
    as.numeric(tapply(po_prob, grid[[paste0("Y", k)]], sum)))
  old_pXY <- pXY; old_pY_list <- pY_list
  pXY <<- pXY_true; pY_list <<- pY_list_true
  out_true <- run_for_obj(obj_spec, obj_name)
  pXY <<- old_pXY; pY_list <<- old_pY_list
  
  true_rows <- out_true$results |>
    dplyr::select(scenario, case, min_val, max_val) |>
    dplyr::mutate(
      case     = paste0(as.character(case), "_true"),
      mean_lb  = min_val, ci_lb_lo = min_val, ci_lb_hi = min_val,
      mean_ub  = max_val, ci_ub_lo = max_val, ci_ub_hi = max_val,
      median_tries = NA_real_,
      N_exp = as.integer(N_exp), N_obs = as.integer(N_obs)
    ) |>
    dplyr::select(scenario, case, mean_lb, ci_lb_lo, ci_lb_hi, mean_ub, ci_ub_lo, ci_ub_hi, median_tries, N_exp, N_obs)
  
  li_true <- NULL
  if (obj_spec$type %in% c("joint","conditional")) {
    old_pXY2 <- pXY; old_pY_list2 <- pY_list
    pXY <<- pXY_true; pY_list <<- pY_list_true
    li_true <- compute_lipearl_bounds_for_obj(obj_spec)
    pXY <<- old_pXY2; pY_list <<- old_pY_list2
  }
  if (!is.null(li_true) && !is.null(li_true$lb) && !is.null(li_true$ub)) {
    true_rows <- dplyr::bind_rows(true_rows, data.frame(
      scenario = "Li–Pearl", case = "both_true",
      mean_lb = as.numeric(li_true$lb), ci_lb_lo = as.numeric(li_true$lb), ci_lb_hi = as.numeric(li_true$lb),
      mean_ub = as.numeric(li_true$ub), ci_ub_lo = as.numeric(li_true$ub), ci_ub_hi = as.numeric(li_true$ub),
      median_tries = NA_real_, N_exp = as.integer(N_exp), N_obs = as.integer(N_obs)
    ))
  }
  
  true_obj_value_from_po <- function(obj_spec, grid, po_prob){
    obj <- make_obj(obj_spec, grid)
    numer <- sum(obj$obj_vec * po_prob)
    denom <- 1
    if (!is.null(obj$denom_lab)) {
      den_idx <- rep(TRUE, nrow(grid))
      if (!is.null(obj_spec$condX)) den_idx <- den_idx & (grid$X == obj_spec$condX)
      if (!is.null(obj_spec$condY)) den_idx <- den_idx & (grid$Y == obj_spec$condY)
      denom <- sum(po_prob[den_idx]); if (denom <= 0) return(NA_real_)
    }
    numer / denom
  }
  true_val <- true_obj_value_from_po(obj_spec, grid, po_prob)
  
  summary_df <- dplyr::bind_rows(summary_df, true_rows) |>
    dplyr::mutate(
      scenario = factor(scenario, levels = c("Li–Pearl", names(constraint_scenarios))),
      case     = factor(case,     levels = CASE_LEVELS),
      true     = true_val,
      N        = as.integer(N_obs)
    ) |>
    dplyr::arrange(scenario, case, N_exp, N_obs)
  
  reps_nested <- split_replicates(rep_df)
  list(replicates = reps_nested, summary = as.data.frame(summary_df))
}



# ========================= Li & Pearl (2024) bounds helpers =========================
.clamp01 <- function(x) pmax(0, pmin(1, x))
.get_pyx <- function(i, j) { pY_list[[j]][i] }      # P(Y_i^{x_j})
.get_pxy <- function(j, i) { pXY[(j-1)*n + i] }     # P(X=j, Y=i)
.get_pX  <- function(j) { sum(pXY[((j-1)*n + 1):(j*n)]) }   # P(X=j)
.get_pY  <- function(i) { sum(pXY[seq(i, m*n, by=n)]) }     # P(Y=i)

.bounds_yixj <- function(i, j) { v <- .get_pyx(i,j); c(lb=v, ub=v) }                     # Thm. ident.
.bounds_PPre1 <- function(i, j) {  # Thm.4
  pyx <- .get_pyx(i,j); pyi <- .get_pY(i); pxj_yi <- .get_pxy(j,i)
  c(lb=.clamp01(max(pxj_yi, pyx+pyi-1)), ub=.clamp01(min(pyx, pyi)))
}
.bounds_PSub1 <- function(i, j, kx) {  # Thm.6
  pyx <- .get_pyx(i,j); pxj_yi <- .get_pxy(j,i); pxj <- .get_pX(j); pxk <- .get_pX(kx)
  c(lb=.clamp01(max(0, pyx - pxj_yi - 1 + pxj + pxk)),
    ub=.clamp01(min(pyx - pxj_yi, pxk)))
}
.bounds_PN1 <- function(i, j, p, q) {  # Thm.7
  pyx <- .get_pyx(i,j); pxp_yq <- .get_pxy(p,q); pxj <- .get_pX(j); pxj_yi <- .get_pxy(j,i)
  c(lb=.clamp01(max(0, pyx + pxp_yq - 1 + pxj - pxj_yi)),
    ub=.clamp01(min(pyx - pxj_yi, pxp_yq)))
}
.bounds_PRep1 <- function(i, j, q) {   # Thm.5
  pyx <- .get_pyx(i,j); pyq <- .get_pY(q); pxj <- .get_pX(j); pxj_yi <- .get_pxy(j,i)
  term3 <- 0
  for (p in setdiff(seq_len(m), j)) term3 <- term3 + max(0, pyx + .get_pxy(p,q) - 1 + pxj - pxj_yi)
  c(lb=.clamp01(max(0, pyx + pyq - 1, term3)),
    ub=.clamp01(min(pyx - pxj_yi, pyq - .get_pxy(j,q))))
}

.bounds_PNSk <- function(yis, js) {    # Thm.8
  k <- length(yis); stopifnot(length(js)==k)
  pyxs <- mapply(.get_pyx, yis, js)
  if (k==1) return(.bounds_yixj(yis[1], js[1]))
  termA  <- sum(pyxs) - k + 1
  termB  <- max(sapply(seq_len(k), function(t) .bounds_PNSk(yis[-t], js[-t])["lb"] + pyxs[t] - 1))
  others <- setdiff(seq_len(m), unique(js))
  sumPN  <- sum(sapply(seq_len(k), function(r) .bounds_PN_k(yis[-r], js[-r], p=js[r], q=yis[r])["lb"]))
  sumSub <- if (length(others)) sum(sapply(others, function(p) .bounds_PSub_k(yis, js, p)["lb"])) else 0
  lb <- max(0, termA, termB, sumPN + sumSub)
  termU1 <- min(pyxs)
  termU2 <- min(sapply(seq_len(k), function(t) .bounds_PNSk(yis[-t], js[-t])["ub"]))
  sumPNu <- sum(sapply(seq_len(k), function(r) .bounds_PN_k(yis[-r], js[-r], p=js[r], q=yis[r])["ub"]))
  sumSubu <- if (length(others)) sum(sapply(others, function(p) .bounds_PSub_k(yis, js, p)["ub"])) else 0
  ub <- min(termU1, termU2, sumPNu + sumSubu)
  c(lb=.clamp01(lb), ub=.clamp01(ub))
}

.bounds_PSub_k <- function(yis, js, p) {   # Thm.9
  k <- length(yis); pyxs <- mapply(.get_pyx, yis, js)
  if (k==1) return(.bounds_PSub1(yis[1], js[1], p))
  termA <- sum(pyxs) + .get_pX(p) - k
  termB <- max(sapply(seq_len(k), function(t) .bounds_PNSk(yis[-t], js[-t])["lb"] + .bounds_PSub1(yis[t], js[t], p)["lb"] - 1))
  lb <- max(0, termA, termB)
  termU <- min(min(pyxs), .get_pX(p),
               min(sapply(seq_len(k), function(t) .bounds_PNSk(yis[-t], js[-t])["ub"])),
               min(sapply(seq_len(k), function(t) .bounds_PSub1(yis[t], js[t], p)["ub"])))
  c(lb=.clamp01(lb), ub=.clamp01(termU))
}

.bounds_PN_k <- function(yis, js, p, q) {  # Thm.11
  k <- length(yis); pyxs <- mapply(.get_pyx, yis, js)
  if (k==1) return(.bounds_PN1(yis[1], js[1], p, q))
  termA <- sum(pyxs) + .get_pxy(p,q) - k
  termB <- max(sapply(seq_len(k), function(t) .bounds_PNSk(yis[-t], js[-t])["lb"] + .bounds_PN1(yis[t], js[t], p, q)["lb"] - 1))
  lb <- max(0, termA, termB)
  termU <- min(min(pyxs), .get_pxy(p,q),
               min(sapply(seq_len(k), function(t) .bounds_PNSk(yis[-t], js[-t])["ub"])),
               min(sapply(seq_len(k), function(t) .bounds_PN1(yis[t], js[t], p, q)["ub"])))
  c(lb=.clamp01(lb), ub=.clamp01(termU))
}

.bounds_PRep_k <- function(yis, js, q) {   # Thm.10
  k <- length(yis); pyxs <- mapply(.get_pyx, yis, js)
  if (k == 1) {
    if (q == yis[1]) return(.bounds_PPre1(yis[1], js[1]))
    return(.bounds_PRep1(yis[1], js[1], q))
  }
  termA <- sum(pyxs) + .get_pY(q) - k
  termB <- max(sapply(seq_len(k), function(t) {
    .bounds_PNSk(yis[-t], js[-t])["lb"] + .bounds_PRep1(yis[t], js[t], q)["lb"] - 1
  }))
  idx_rq <- which(yis == q)
  sumPN1 <- if (length(idx_rq)) {
    sum(sapply(idx_rq, function(r) .bounds_PN_k(yis[-r], js[-r], p = js[r], q = q)["lb"]))
  } else 0
  others <- setdiff(seq_len(m), unique(js))
  sumPN2 <- if (length(others)) sum(sapply(others, function(p) .bounds_PN_k(yis, js, p = p, q = q)["lb"])) else 0
  lb <- max(0, termA, termB, sumPN1 + sumPN2)
  termU <- min(
    min(pyxs), .get_pY(q),
    min(sapply(seq_len(k), function(t) .bounds_PNSk(yis[-t], js[-t])["ub"])),
    min(sapply(seq_len(k), function(t) .bounds_PRep1(yis[t], js[t], q)["ub"])),
    {
      sumU1 <- if (length(idx_rq)) sum(sapply(idx_rq, function(r) .bounds_PN_k(yis[-r], js[-r], p = js[r], q = q)["ub"])) else 0
      sumU2 <- if (length(others)) sum(sapply(others, function(p) .bounds_PN_k(yis, js, p = p, q = q)["ub"])) else 0
      sumU1 + sumU2
    }
  )
  c(lb = .clamp01(lb), ub = .clamp01(termU))
}

compute_lipearl_bounds_for_obj <- function(obj_spec) {
  if (!(obj_spec$type %in% c("joint","conditional"))) return(NULL)
  if (!is.null(obj_spec$target_ineq)) return(NULL)
  if (is.null(obj_spec$target_eq)) return(NULL)
  eq_idx <- which(!is.na(obj_spec$target_eq)); if (!length(eq_idx)) return(NULL)
  yis <- as.integer(obj_spec$target_eq[eq_idx]); js <- as.integer(eq_idx)
  hasX <- !is.null(obj_spec$condX); hasY <- !is.null(obj_spec$condY)
  compute_joint <- function() {
    if (!hasX && !hasY) {
      .bounds_PNSk(yis, js)
    } else if (hasX && !hasY) {
      .bounds_PSub_k(yis, js, p = obj_spec$condX)
    } else if (!hasX && hasY) {
      .bounds_PRep_k(yis, js, q = obj_spec$condY)
    } else {
      .bounds_PN_k(yis, js, p = obj_spec$condX, q = obj_spec$condY)
    }
  }
  b_joint <- compute_joint()
  if (obj_spec$type == "joint") return(list(lb = unname(b_joint["lb"]), ub = unname(b_joint["ub"])))
  denom <- 1
  if (hasX && hasY)      denom <- .get_pxy(obj_spec$condX, obj_spec$condY)
  else if (hasX)         denom <- .get_pX(obj_spec$condX)
  else if (hasY)         denom <- .get_pY(obj_spec$condY)
  if (is.na(denom) || denom <= 0) return(list(lb = NA_real_, ub = NA_real_))
  list(lb = unname(b_joint["lb"]) / denom, ub = unname(b_joint["ub"]) / denom)
}

#──────────────────────── 8.6 実行ラッパ ──────────────────────#
is_df_like <- function(x) inherits(x, c("data.frame","tbl_df"))
is_atomic_like <- function(x) is.atomic(x) || is.matrix(x) || is_df_like(x)
deep_merge <- function(x, y) {
  if (!is.list(x) || is_atomic_like(x) || is_atomic_like(y)) return(y)
  for (nm in names(y)) x[[nm]] <- if (is.null(x[[nm]])) y[[nm]] else deep_merge(x[[nm]], y[[nm]])
  x
}

make_master_bar <- function(total_steps) {
  progress::progress_bar$new(
    format = "[:bar] :percent | :current/:total | :elapsed | ETA: :eta | :phase :obj r=:r/:M Nexp=:Nexp Nobs=:Nobs tries=:tries Σ=:sumtries",
    total  = as.integer(ifelse(is.finite(total_steps) && total_steps > 0, total_steps, 1L)),
    clear  = FALSE, width = 90
  )
}


run_all <- function(obj_specs, N_exp_values, N_obs_values, M, workers = 1) {
  stopifnot(length(N_exp_values) == length(N_obs_values))
  out <- list()
  for (obj_name in names(obj_specs)) {
    out[[obj_name]] <- list()
    for (i in seq_along(N_exp_values)) {
      Nexp <- as.integer(N_exp_values[i]); Nobs <- as.integer(N_obs_values[i])
      keyNexp <- sprintf("Nexp=%d", Nexp)
      keyNobs <- sprintf("Nobs=%d", Nobs)
      res <- simulate_many(obj_name, obj_specs[[obj_name]], N_exp = Nexp, N_obs = Nobs, M = as.integer(M))
      M_key <- sprintf("M=%d", as.integer(M))
      if (is.null(out[[obj_name]][[keyNexp]])) out[[obj_name]][[keyNexp]] <- list()
      if (is.null(out[[obj_name]][[keyNexp]][[keyNobs]])) out[[obj_name]][[keyNexp]][[keyNobs]] <- list()
      out[[obj_name]][[keyNexp]][[keyNobs]][[M_key]] <- res
    }
    out[[obj_name]][["summary_allN"]] <- build_summary_allN(out[[obj_name]])
  }
  out
}

add_runs <- function(obj_specs, N_exp_values, N_obs_values, M, workers = 1) {
  stopifnot(length(N_exp_values) == length(N_obs_values))
  need_exp <- vapply(as.integer(N_exp_values), function(N) {
    bank <- get_sampling_bank_exp(N); have <- if (is.null(bank)) 0L else length(bank$samples)
    max(0L, as.integer(M) - have)
  }, integer(1L))
  need_obs <- vapply(as.integer(N_obs_values), function(N) {
    bank <- get_sampling_bank_obs(N); have <- if (is.null(bank)) 0L else length(bank$samples)
    max(0L, as.integer(M) - have)
  }, integer(1L))
  total_sampling_steps <- sum(need_exp) + sum(need_obs)
  total_opt_steps      <- length(obj_specs) * length(N_exp_values) * as.integer(M)
  total_steps          <- total_sampling_steps + total_opt_steps
  pb <- make_master_bar(total_steps)
  
  new_out <- list()
  task_total <- length(obj_specs) * length(N_exp_values)
  task_idx   <- 0L
  
  for (obj_name in names(obj_specs)) {
    new_out[[obj_name]] <- list()
    for (i in seq_along(N_exp_values)) {
      Nexp <- as.integer(N_exp_values[i]); Nobs <- as.integer(N_obs_values[i])
      task_idx <- task_idx + 1L
      cat(sprintf("\n========== [%d/%d] sampling | %s | Nexp=%d | Nobs=%d ==========\n",
                  as.integer(task_idx), as.integer(task_total), as.character(obj_name), Nexp, Nobs))
      ensure_sampling_bank_exp(Nexp, M, workers = workers, pb = pb)
      ensure_sampling_bank_obs(Nobs, M, workers = workers, pb = pb)
      
      cat(sprintf("---------- [%d/%d] optimize | %s | Nexp=%d Nobs=%d (M=%d) ----------\n",
                  as.integer(task_idx), as.integer(task_total), as.character(obj_name), Nexp, Nobs, as.integer(M)))
      keyNexp <- sprintf("Nexp=%d", Nexp)
      keyNobs <- sprintf("Nobs=%d", Nobs)
      res <- simulate_many(obj_name = obj_name, obj_spec = obj_specs[[obj_name]],
                           N_exp = Nexp, N_obs = Nobs, M = as.integer(M), pb = pb)
      M_key <- sprintf("M=%d", as.integer(M))
      if (is.null(new_out[[obj_name]][[keyNexp]])) new_out[[obj_name]][[keyNexp]] <- list()
      if (is.null(new_out[[obj_name]][[keyNexp]][[keyNobs]])) new_out[[obj_name]][[keyNexp]][[keyNobs]] <- list()
      new_out[[obj_name]][[keyNexp]][[keyNobs]][[M_key]] <- res
    }
    new_out[[obj_name]][["summary_allN"]] <- build_summary_allN(new_out[[obj_name]])
  }
  
  if (!exists("0909revised_RESULT_bounds", envir = .GlobalEnv)) {
    assign("0909revised_RESULT_bounds", new_out, envir = .GlobalEnv)
    assign("RESULT_bounds_0909revised",  new_out, envir = .GlobalEnv)
  } else {
    merged <- deep_merge(get("0909revised_RESULT_bounds", envir = .GlobalEnv), new_out)
    for (obj_name in names(merged)) {
      if (is.list(merged[[obj_name]])) {
        merged[[obj_name]][["summary_allN"]] <- build_summary_allN(merged[[obj_name]])
      }
    }
    assign("0909revised_RESULT_bounds", merged, envir = .GlobalEnv)
    assign("RESULT_bounds_0909revised", merged, envir = .GlobalEnv)
  }
  cat("\nStored:", paste(names(new_out), collapse = ", "),
      "for (Nexp,Nobs)=", paste(sprintf("(%d,%d)", as.integer(N_exp_values), as.integer(N_obs_values)), collapse = ", "),
      "M=", M, "workers=", workers, "\n")
}


#──────────────────────── 実行例 ────────────────────────#
workers <- max(1, parallel::detectCores() - 2)
future::plan(future::multisession, workers = workers)

# 例：N_exp と N_obs を同一系列で指定（必要に応じて別系列でも可；長さは一致させる）
N_exp_values <- c(10, 100, 1000, 10000)
N_obs_values <- c(10, 100, 1000, 10000)
M <- 100

add_runs(obj_specs, N_exp_values, N_obs_values, M, workers)

# 並列実行が終わったら
future::plan(sequential)
invisible(gc())













# ===============================================================
# NEW: Table7/8 仕様の 1-tabular 出力（{cc|cccc|c}）
# - 入力: 0830revised2_RESULT_bounds（あなたの既存オブジェクト）
# - 目的関数ごとに case=exp/obs/both の tabular を個別 .tex 出力
# - 出力先: tex/bounds
# - Assumption 列は固定対応：
#   (i) none, (ii) $Y_0 \leq Y_1$, (iii) $Y_1 \leq Y_2$, (iv) $Y_0 \leq Y_1 \leq Y_2$
#   ※ both のときのみ Li–Pearl を (i) として先頭に追加（文言はそのまま）
# - Bounds 列は LB / UB の2行
# - 不等号は \leq を使用
# - ヘッダまわりは \hline\hline を入れる
# ===============================================================

# ---------- 小道具 ----------
.dir_ensure <- function(p){ if(!dir.exists(p)) dir.create(p, recursive=TRUE, showWarnings=FALSE); p }
.norm <- function(x){ gsub("[^a-z0-9]+","", tolower(as.character(x))) }

# 小数を丸めて "-0.000" を "0.000" に直す共通整形
.fmt_num <- function(x, digits = 3){
  z <- round(as.numeric(x), digits)     # まず丸め
  z[abs(z) < 10^(-digits)] <- 0         # -0 を 0 に補正（安全側ガード）
  sprintf(paste0("%.", digits, "f"), z)
}

# 信頼区間セルの整形（カンマ後スペースなし、-0.000対策込み）
fmt_cell_bounds <- function(m, lo, hi, digits = 3){
  if (any(is.na(c(m, lo, hi)))) return("")
  paste0(.fmt_num(m, digits), " [", .fmt_num(lo, digits), ",", .fmt_num(hi, digits), "]")
}


# 目的関数ノードから「大きなサマリー」を取り出し、N 列を保証
.get_summary_Nfirst <- function(result_obj, obj_name){
  node <- result_obj[[obj_name]]
  if (is.null(node)) return(data.frame())
  # 新形式: summary_allN がそのまま使える（既に N 列あり）
  if (is.data.frame(node$summary_allN) && nrow(node$summary_allN)>0) {
    return(node$summary_allN)
  }
  # 旧入れ子: N=... / M=... 以下を平坦化し N を作る
  rows <- list()
  for (kN in names(node)){
    if (!grepl("^N=", kN)) next
    Nval <- suppressWarnings(as.integer(sub("^N=([0-9]+)$","\\1", kN)))
    subN <- node[[kN]]
    if (!is.list(subN)) next
    for (Mk in names(subN)){
      sm <- subN[[Mk]]$summary
      if (is.null(sm) || !nrow(sm)) next
      sm$N <- Nval
      rows[[paste(kN,Mk,sep=":")]] <- sm
    }
  }
  if (!length(rows)) return(data.frame())
  dplyr::bind_rows(rows)
}

# True value をケースごとに 1 数値へ
.get_true_value <- function(df, case_name){
  d <- df[.norm(df$case)==.norm(case_name), , drop=FALSE]
  if ("true" %in% names(d)) {
    tv <- unique(d$true); tv <- tv[!is.na(tv)]
    if (length(tv)>=1) return(tv[1])
  }
  dtrue <- df[.norm(df$case)==.norm(paste0(case_name,"_true")), , drop=FALSE]
  if (nrow(dtrue)) {
    v <- unique(c(dtrue$mean_lb, dtrue$mean_ub)); v <- v[!is.na(v)]
    if (length(v)>=1) return(v[1])
  }
  NA_real_
}

# シナリオ名のゆれ吸収（→内部キー）
.scen_key <- function(s){
  s0 <- tolower(gsub("\\s+","", s))
  s0 <- gsub("\\.a\\.s\\.|a\\.s\\.|a\\.?s\\.?","", s0)
  s0 <- gsub("≤","<=", s0, fixed=TRUE)
  s0 <- gsub("leq","<=", s0, fixed=TRUE)
  s0 <- gsub("<=+","<=", s0)
  s0
}

# 表示ラベル（Assumption 列）
label_assumption <- function(key){
  switch(key,
         "none"                = "(i) ",
         "y0<=y1"              = "(ii)",
         "y1<=y2"              = "(iii)",
         "y0<=y1<=y2"          = "(iv)",
         "li–pearl"            = "(i) Li--Pearl",
         "li-pearl"            = "(i) Li--Pearl",
         # fallback
         key
  )
}

# df から (case, scenario_key, N) に一致する1行を拾う
.pick_row <- function(df, case_name, scen_key, N){
  d <- df[.norm(df$case)==.norm(case_name), , drop=FALSE]
  if (!nrow(d)) return(NULL)
  # シナリオ正規化
  skey <- vapply(d$scenario, .scen_key, "")
  # 代表的キーに丸め
  skey <- sub("^y0\\s*<=\\s*y1\\s*a?s?\\.?$","y0<=y1", skey)
  skey <- sub("^y1\\s*<=\\s*y2\\s*a?s?\\.?$","y1<=y2", skey)
  skey <- sub("^y0\\s*<=\\s*y1\\s*<=\\s*y2\\s*a?s?\\.?$","y0<=y1<=y2", skey)
  skey <- sub("^none$|^noadditionalassumption$|^baseline$","none", skey)
  skey <- sub("^li[ -–]?pearl.*$","li–pearl", skey)
  d$skey <- skey
  
  cnd <- d[d$skey==skey[1] & FALSE,] # empty template
  
  # N優先
  if ("N" %in% names(d)) {
    r <- d[d$skey==skey[ which(d$skey==scen_key)[1] ] & as.integer(d$N)==as.integer(N), , drop=FALSE]
    if (nrow(r)) return(r[1,,drop=FALSE])
  }
  # 旧: N_obs / N_exp から近いもの
  if ("N_obs" %in% names(d)) {
    r <- d[d$skey==scen_key & as.integer(d$N_obs)==as.integer(N), , drop=FALSE]
    if (nrow(r)) return(r[1,,drop=FALSE])
  }
  if ("N_exp" %in% names(d)) {
    exp_all <- paste(N,N,N, sep="-")
    r <- d[d$skey==scen_key & .norm(d$N_exp)==.norm(exp_all), , drop=FALSE]
    if (nrow(r)) return(r[1,,drop=FALSE])
  }
  # どれも無ければそのシナリオの先頭
  r <- d[d$skey==scen_key, , drop=FALSE]
  if (nrow(r)) return(r[1,,drop=FALSE])
  NULL
}

# 1 tabular を作る
# --- 置き換え版：Table7/8 の1-tabular生成 ---
# --- 置き換え版：Table7/8 の1-tabular生成（ヘッダ表記を調整） ---
build_tabular_case <- function(df, case_name,
                               Ns = c(10,100,1000,10000), digits=3,
                               include_li_pearl = (tolower(case_name)=="both")){
  stopifnot(is.data.frame(df))
  need <- c("scenario","case","mean_lb","ci_lb_lo","ci_lb_hi","mean_ub","ci_ub_lo","ci_ub_hi","N")
  miss <- setdiff(need, names(df))
  if (length(miss)) stop("summary に必要列がありません: ", paste(miss, collapse=", "))
  
  Ns_keep  <- Ns
  colspec  <- "{cc|cccc}"                      # ← True 列を削除
  hdrNs    <- paste(sprintf("$N=%s$", Ns_keep), collapse=" & ")
  
  scen_list <- c("none","y0<=y1","y1<=y2","y0<=y1<=y2")
  if (include_li_pearl) scen_list <- c("li–pearl", scen_list)
  
  bounds_hdr <- switch(tolower(case_name),
                       "exp"  = "Bounds (Exp.)",
                       "obs"  = "Bounds (Obs.)",
                       "both" = "Bounds (Both)",
                       paste0("Bounds (", case_name, ")"))
  
  body_parts <- character(0)
  for (ii in seq_along(scen_list)) {
    sk <- scen_list[ii]
    cells_lb <- character(length(Ns_keep))
    for (j in seq_along(Ns_keep)) {
      r <- .pick_row(df, case_name, sk, Ns_keep[j])
      cells_lb[j] <- if (is.null(r)) "" else fmt_cell_bounds(r$mean_lb, r$ci_lb_lo, r$ci_lb_hi, digits)
    }
    line_lb <- paste(label_assumption(sk), "LB", paste(cells_lb, collapse=" & "), sep=" & ")
    
    cells_ub <- character(length(Ns_keep))
    for (j in seq_along(Ns_keep)) {
      r <- .pick_row(df, case_name, sk, Ns_keep[j])
      cells_ub[j] <- if (is.null(r)) "" else fmt_cell_bounds(r$mean_ub, r$ci_ub_lo, r$ci_ub_hi, digits)
    }
    line_ub <- paste(label_assumption(sk), "UB", paste(cells_ub, collapse=" & "), sep=" & ")
    
    body_parts <- c(body_parts, paste0(line_lb, " \\\\"), paste0(line_ub, " \\\\"))
    if (ii < length(scen_list)) body_parts <- c(body_parts, "\\hline")
  }
  
  paste0(
    "\\begin{tabular}", colspec, "\n",
    "\\hline\n",
    "Assump. & ", bounds_hdr, " & ", hdrNs, " \\\\\n",   # ← True 列見出しを削除
    "\\hline\n",
    "\\hline\n",
    paste(body_parts, collapse = "\n"), "\n",
    "\\hline\n",
    "\\end{tabular}\n"
  )
}




# ---------- エクスポート（Table7/8） ----------
# 目的関数名 → ファイル名（最小限サニタイズ）
# 目的関数名 → 安全なファイル名
.filename_from_obj <- function(s){
  s <- gsub("\\s+", "", s)    # 空白除去
  s <- gsub("\\[", "(", s)    # [ → (
  s <- gsub("\\]", ")", s)    # ] → )
  s <- gsub("\\|", "_", s)    # | → _
  s <- gsub("/|\\\\", "_", s) # / と \ → _
  s <- gsub("[:*?\"<>]", "_", s) # 残りのNG記号 → _
  s
}


export_table78_bounds <- function(result_obj,
                                  obj_for_tbl7 = "P(Y0=0,Y1=0,Y2=1)",
                                  obj_for_tbl8 = "E[Y1-Y0 | X=2,Y=2]",
                                  Ns = c(10,100,1000,10000),
                                  digits = 3,
                                  out_dir = file.path("tex","bounds")){
  .dir_ensure(out_dir)
  
  # ---- Table 7: 目的関数ごとに exp/obs/both を出力 ----
  df7 <- .get_summary_Nfirst(result_obj, obj_for_tbl7)
  if (nrow(df7)) {
    base7 <- .filename_from_obj(gsub("\\s*\\|\\s*", "|", obj_for_tbl7))  # | の両側の空白は整形
    for (cs in c("exp","obs","both")) {
      if (!any(.norm(df7$case)==.norm(cs))) next
      tex <- build_tabular_case(df7, cs, Ns=Ns, digits=digits, include_li_pearl=(cs=="both"))
      writeLines(tex, file.path(out_dir, sprintf("%s_%s.tex", base7, cs)), useBytes=TRUE)
    }
  }
  
  # ---- Table 8: 目的関数ごとに obs/both を出力 ----
  df8 <- .get_summary_Nfirst(result_obj, obj_for_tbl8)
  if (nrow(df8)) {
    # 「|」の周囲のスペースは整えてからサニタイズ（見栄え用）
    base8 <- .filename_from_obj(gsub("\\s*\\|\\s*", "|", obj_for_tbl8))
    for (cs in c("obs","both")) {
      if (!any(.norm(df8$case)==.norm(cs))) next
      tex <- build_tabular_case(df8, cs, Ns=Ns, digits=digits, include_li_pearl=(cs=="both"))
      writeLines(tex, file.path(out_dir, sprintf("%s_%s.tex", base8, cs)), useBytes=TRUE)
    }
  }
  
  invisible(TRUE)
}


# ---------- 実行例 ----------
# 必要なら Ns を調整してください（列は {cc|cccc} 前提で4本）
export_table78_bounds(
  result_obj   = `0909revised_RESULT_bounds`,
  obj_for_tbl7 = "P(Y0=0,Y1=0,Y2=1)",
  obj_for_tbl8 = "E[Y1-Y0 | X=2,Y=2]",
  Ns           = c(10,100,1000,10000),
  digits       = 3,
  out_dir      = file.path("tex","bounds")
)


