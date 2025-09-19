#──────────────────────── 0. ライブラリ ────────────────────────#
# install.packages(c("Matrix","Rglpk","dplyr","tidyr","e1071","purrr","tibble",
#                    "future","future.apply","progress","parallel"))
library(Matrix); library(Rglpk); library(dplyr); library(tidyr); library(e1071)
library(purrr);  library(tibble); library(parallel)
library(future); library(future.apply); library(progress)

# ────────── 小道具 ──────────
.init_list_once <- function(name) { if (!exists(name, envir=.GlobalEnv)) assign(name, list(), envir=.GlobalEnv) }
`%||%` <- function(x, y) if (is.null(x)) y else x
.fmt_num <- function(x, digits=0){ if (is.na(x)) return(""); z <- round(as.numeric(x), digits); z[abs(z) < 10^(-digits)] <- 0; sprintf(paste0("%.",digits,"f"), z) }

# ===== 結果シンクのレジストリ =====
.RESULT_SINKS <- new.env(parent = emptyenv())
.RESULT_SINKS$bounds         <- "0909revised_RESULT_bounds"          # 本番の境界結果
.RESULT_SINKS$bounds_TIMING  <- "0909revised_RESULT_bounds_TIMING"   # 計測用境界結果
.RESULT_SINKS$times          <- "0909revised_RESULT_times"           # LP実行時間ログ
.RESULT_SINKS$sampling       <- "0909revised_RESULT_sampling_times"  # サンプリング時間ログ
for (nm in as.list(.RESULT_SINKS)) .init_list_once(nm)

.refresh_result_aliases <- function() {
  assign("RESULT_bounds_0909revised",         get(.RESULT_SINKS$bounds,         envir=.GlobalEnv), envir=.GlobalEnv)
  assign("RESULT_bounds_0909revised_TIMING",  get(.RESULT_SINKS$bounds_TIMING,  envir=.GlobalEnv), envir=.GlobalEnv)
  assign("RESULT_times_0909revised",          get(.RESULT_SINKS$times,          envir=.GlobalEnv), envir=.GlobalEnv)
  assign("RESULT_sampling_times_0909revised", get(.RESULT_SINKS$sampling,       envir=.GlobalEnv), envir=.GlobalEnv)
}
.refresh_result_aliases()

# サンプリング・バンク（Exp/Obs）と共通ペアのルート
.init_list_once("0909revised_SAMPLING_BANK_EXP")
.init_list_once("0909revised_SAMPLING_BANK_OBS")
.init_list_once("0909revised_COMMON_PAIRS")

#──────────────────────── 1. 基本パラメータ ──────────────────#
m <- 3     # 潜在反応変数の本数 (Y1..Ym)
n <- 3     # 各 Y の水準数

#──────────────────────── 2. グリッド生成 ───────────────────#
Y_list <- setNames(lapply(seq_len(m), \(.) seq_len(n)), paste0("Y", seq_len(m)))
grid <- do.call(expand.grid, c(Y_list, list(X = seq_len(m)), list(Y = seq_len(n))))
Z <- nrow(grid)

# ケース名（順序固定）
CASE_LEVELS <- c("exp", "obs", "both", "exp_true", "obs_true", "both_true")

#──────────────────────── 3. ユーティリティ ──────────────────#
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
  Yi <- grid[[paste0("Y", i)]]; Yj <- grid[[paste0("Y", j)]]
  switch(rel,
         "<"  = which(Yi <  Yj),
         "<=" = which(Yi <= Yj),
         "="  = which(Yi == Yj),
         ">=" = which(Yi >= Yj),
         ">"  = which(Yi >  Yj),
         integer(0))
}
marginal_mat <- function(idx_list, Z){
  rows <- rep(seq_along(idx_list), lengths(idx_list))
  cols <- unlist(idx_list)
  sparseMatrix(i = rows, j = cols, x = 1, dims = c(length(idx_list), Z))
}
band_idx <- function(grid, m, k) {
  ok <- rep(TRUE, nrow(grid))
  for (i in seq_len(m)) for (j in seq_len(i-1)) {
    Yi <- grid[[paste0("Y", i)]]; Yj <- grid[[paste0("Y", j)]]
    ok <- ok & (Yi - Yj >= 0) & (Yi - Yj <= k); if (!any(ok)) return(integer(0))
  }
  which(ok)
}
event_blocks_from_idx <- function(idx, lb=NULL, ub=NULL, grid) {
  if (is.null(idx)) return(list())
  if (is.list(idx)) idx <- unlist(idx, recursive=TRUE, use.names=FALSE)
  idx <- as.integer(idx); idx <- idx[is.finite(idx) & !is.na(idx)]
  Zloc <- nrow(grid); idx <- idx[idx >= 1L & idx <= Zloc]
  if (!length(idx)) return(list())
  row1 <- sparseMatrix(i = rep(1L, length(idx)), j = idx, x = 1, dims = c(1L, Zloc))
  out <- list()
  if (!is.null(lb)) out$lb_event <- list(mat=row1, dir=">=", rhs=lb)
  if (!is.null(ub)) out$ub_event <- list(mat=row1, dir="<=", rhs=ub)
  out
}
relation_blocks <- function(rel_mat, lb, ub, grid) {
  idx_all <- seq_len(nrow(grid))
  for (i in seq_len(nrow(rel_mat))) for (j in seq_len(ncol(rel_mat))) {
    rel <- rel_mat[i, j]; if (is.na(rel)) next
    idx_all <- intersect(idx_all, relation_idx(grid, i, j, rel))
  }
  Zloc <- nrow(grid)
  if (!length(idx_all)) {
    out <- list()
    if (!is.null(lb)) out$lb_event <- list(mat=Matrix(0,1,Zloc,sparse=TRUE), dir=">=", rhs=lb)
    if (!is.null(ub)) out$ub_event <- list(mat=Matrix(0,1,Zloc,sparse=TRUE), dir="<=", rhs=ub)
    return(out)
  }
  row1 <- sparseMatrix(i=rep(1L,length(idx_all)), j=as.integer(idx_all), x=1, dims=c(1L, Zloc))
  blocks <- list()
  if(!is.null(lb)) blocks$lb_event <- list(mat=row1, dir=">=", rhs=lb)
  if(!is.null(ub)) blocks$ub_event <- list(mat=row1, dir="<=", rhs=ub)
  blocks
}
compile_blocks <- function(blocks){
  mats <- lapply(blocks, `[[`, "mat"); dirs <- lapply(blocks, `[[`, "dir"); rhs <- lapply(blocks, `[[`, "rhs")
  keep <- vapply(mats, function(M) !is.null(M) && nrow(M) > 0, logical(1))
  mats_kept <- lapply(mats[keep], function(M) if (inherits(M,"dgCMatrix")) M else as(M,"dgCMatrix"))
  A <- if (length(mats_kept)) do.call(rbind, mats_kept) else Matrix(0,0,0, sparse=TRUE)
  list(A=A, dir=unlist(dirs[keep], use.names=FALSE), rhs=unlist(rhs[keep], use.names=FALSE))
}
pb_tick_safe <- function(pb, tokens=NULL){ if (is.null(pb)) return(invisible(NULL)); try(pb$tick(tokens=tokens), silent=TRUE); invisible(NULL) }

# ────────── 目的関数 → ベクトル化 ──────────
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
  if (obj_spec$type == "conditional" || obj_spec$type == "joint") {
    if (!is.null(obj_spec$target_eq)) {
      eq_idx <- which(!is.na(obj_spec$target_eq))
      eq_list <- lapply(eq_idx, function(i) list(var=i, op="==", val=obj_spec$target_eq[i]))
      v <- apply_conditions(v, grid, eq_list)
    }
    if (!is.null(obj_spec$target_ineq)) v <- apply_conditions(v, grid, obj_spec$target_ineq)
    if (!is.null(obj_spec$condX)) v <- v & (grid$X == obj_spec$condX)
    if (!is.null(obj_spec$condY)) v <- v & (grid$Y == obj_spec$condY)
    obj_vec <- as.integer(v)
    if (obj_spec$type == "joint") {
      labels <- character()
      if (!is.null(obj_spec$target_eq)) {
        eq_idx <- which(!is.na(obj_spec$target_eq))
        labels <- c(labels, paste0("Y", eq_idx, "=", obj_spec$target_eq[eq_idx]))
      }
      if (!is.null(obj_spec$target_ineq))
        labels <- c(labels, vapply(obj_spec$target_ineq, function(c) paste0("Y",c$var,c$op,c$val), ""))
      base_label <- if(length(labels)>0) paste(labels, collapse=",") else "Y1…Ym"
      cond_label <- if(!is.null(obj_spec$condX)&&!is.null(obj_spec$condY)) sprintf("|X=%d,Y=%d", obj_spec$condX, obj_spec$condY) else ""
      return(list(obj_vec=obj_vec, denom_lab=NULL, obj_label=sprintf("P(%s%s)", base_label, cond_label)))
    } else {
      denom_lab <- NULL
      if (!is.null(obj_spec$condX) && !is.null(obj_spec$condY)) denom_lab <- sprintf("obs_k%d_y%d", obj_spec$condX, obj_spec$condY)
      else if (!is.null(obj_spec$condX)) denom_lab <- sprintf("obs_k%d_yALL", obj_spec$condX)
      else if (!is.null(obj_spec$condY)) denom_lab <- sprintf("obs_kALL_y%d", obj_spec$condY)
      labels <- character()
      if (!is.null(obj_spec$target_eq)) {
        eq_idx <- which(!is.na(obj_spec$target_eq))
        labels <- c(labels, paste0("Y", eq_idx, "=", obj_spec$target_eq[eq_idx]))
      }
      if (!is.null(obj_spec$target_ineq))
        labels <- c(labels, vapply(obj_spec$target_ineq, function(c) paste0("Y",c$var,c$op,c$val), ""))
      target_label <- if(length(labels)>0) paste(labels, collapse=",") else "ALL"
      cond_parts <- character()
      if (!is.null(obj_spec$condX)) cond_parts <- c(cond_parts, sprintf("X=%d", obj_spec$condX))
      if (!is.null(obj_spec$condY)) cond_parts <- c(cond_parts, sprintf("Y=%d", obj_spec$condY))
      cond_label <- if(length(cond_parts)>0) paste0("|", paste(cond_parts, collapse=",")) else ""
      return(list(obj_vec=obj_vec, denom_lab=denom_lab, obj_label=sprintf("P(%s%s)", target_label, cond_label)))
    }
  } else if (obj_spec$type == "linear") {
    Zloc <- nrow(grid); cond_mask <- rep(TRUE, Zloc)
    if (!is.null(obj_spec$condX)) cond_mask <- cond_mask & (grid$X == obj_spec$condX)
    if (!is.null(obj_spec$condY)) cond_mask <- cond_mask & (grid$Y == obj_spec$condY)
    if (!is.null(obj_spec$w_vec)) {
      stopifnot(length(obj_spec$w_vec) == Zloc); w <- as.numeric(obj_spec$w_vec)
    } else {
      stopifnot(length(obj_spec$var_coefs) == m)
      intercept <- if (!is.null(obj_spec$intercept)) as.numeric(obj_spec$intercept) else 0
      zero_based <- isTRUE(obj_spec$zero_based)
      y_mat <- sapply(seq_len(m), function(k) {
        vals <- as.numeric(grid[[paste0("Y", k)]]); if (zero_based) vals <- vals - 1; vals
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
      parts <- c(); if (!is.null(obj_spec$condX)) parts <- c(parts, sprintf("X=%d", obj_spec$condX - 1))
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
  "E[Y1-Y0 | X=2,Y=2]" = list(type="linear", var_coefs=c(-1,1,0), intercept=0, zero_based=TRUE, condX=3, condY=3, label_override="E[Y1-Y0|X=2,Y=2]"),
  "P(Y0=1,Y1=0,Y2=1,X=1,Y=0)" = list(type="joint", target_eq=c(2,1,2), target_ineq=NULL, condX=2, condY=1)
)

#──────────────────────── 4. シナリオ定義・基本行列 ───────────────#
idx_exp <- idx_obs <- vector("list", m*n); cnt <- 1
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
zero_mat <- function(idx, Z){ if(length(idx)==0) return(NULL); sparseMatrix(i=seq_along(idx), j=idx, x=1, dims=c(length(idx), Z)) }
base_blocks <- list(sum = list(mat = Matrix(1,1,Z,sparse=TRUE), dir="==", rhs=1),
                    zero = list(mat = zero_mat(bad_rows, Z), dir = rep("==", length(bad_rows)), rhs = rep(0, length(bad_rows))))

#（unusedを本体から削除）

# シナリオ（関係制約）
{
  NAm <- matrix(NA_character_, nrow=m, ncol=m)
  tbl_none  <- NAm
  tbl_0Lq2  <- NAm; tbl_0Lq2[1,3] <- "<="
  tbl_0Lq1  <- NAm; tbl_0Lq1[1,2] <- "<="
  tbl_1Lq2  <- NAm; tbl_1Lq2[2,3] <- "<="
  tbl_chain <- NAm; tbl_chain[1,2] <- "<="; tbl_chain[2,3] <- "<="
  constraint_scenarios <- list()
  constraint_scenarios[["none"]]               <- list(rel_mat=tbl_none,  lb=NULL, ub=NULL)
  constraint_scenarios[["Y0<=Y1 a.s."]]        <- list(rel_mat=tbl_0Lq1, lb=1,    ub=NULL)
  constraint_scenarios[["Y1<=Y2 a.s."]]        <- list(rel_mat=tbl_1Lq2, lb=1,    ub=NULL)
  constraint_scenarios[["Y0<=Y1<=Y2 a.s."]]    <- list(rel_mat=tbl_chain, lb=1,   ub=NULL)
}

#──────────────────────── 5. 真のPO分布 ───────────────────────#
a_xy <- matrix(c(
  0.15, 0.1, 0.1,
  0.1,  0.2, 0.1,
  0.05, 0.1, 0.1
), nrow=m, ncol=n, byrow=TRUE)
a_xy <- a_xy / sum(a_xy)

enforce_monotone_true <- TRUE
good_idx <- {
  base_ok <- setdiff(seq_len(nrow(grid)), consistency_bad(grid, m))
  if (enforce_monotone_true) intersect(base_ok, monotone_idx(grid, m)) else base_ok
}
denom_xy <- table(factor(grid$X[good_idx], levels=seq_len(m)), factor(grid$Y[good_idx], levels=seq_len(n)))
denom_xy <- as.matrix(denom_xy); if (any(denom_xy == 0)) stop("Some (x,y) cells zero under monotonicity+consistency.")
po_prob <- numeric(Z); ix <- good_idx
po_prob[ix] <- a_xy[cbind(grid$X[ix], grid$Y[ix])] / denom_xy[cbind(grid$X[ix], grid$Y[ix])]
stopifnot(abs(sum(po_prob) - 1) < 1e-12)
pxy_mat <- tapply(po_prob, list(grid$X, grid$Y), sum); pXY <- as.vector(t(pxy_mat))
pY_list <- lapply(seq_len(m), function(k) as.numeric(tapply(po_prob, grid[[paste0("Y", k)]], sum)))

#──────────────────────── 6. LP ラッパ ─────────────────────────#
run_lp_safe <- function(obj, A, dir, rhs, maximise=FALSE){
  ctrl1 <- list(canonicalize_status=TRUE, presolve=TRUE,  verbose=FALSE, tm_limit=0)
  ctrl2 <- list(canonicalize_status=TRUE, presolve=FALSE, verbose=FALSE, tm_limit=0)
  bounds <- list(lower=list(ind=seq_len(length(obj)), val=rep(0,length(obj))),
                 upper=list(ind=seq_len(length(obj)), val=rep(1,length(obj))))
  .solve <- function(ctrl) Rglpk::Rglpk_solve_LP(obj=obj, mat=A, dir=dir, rhs=rhs, bounds=bounds, max=maximise, control=ctrl)
  sol <- .solve(ctrl1); if (!is.null(sol$status) && sol$status==0) return(sol)
  .solve(ctrl2)
}

#──────────────────────── 7. Feasible 判定 ─────────────────────#
feasibility_core <- function(b_exp=NULL, b_obs=NULL, apply_to=c("exp","obs","both")){
  for (sname in names(constraint_scenarios)) {
    sc <- constraint_scenarios[[sname]]
    at <- if (is.null(sc$apply_to)) c("exp","obs","both") else sc$apply_to
    at <- intersect(at, apply_to); if (!length(at)) next
    rel_blks_base <- list()
    if (!is.null(sc$rel_mat))  rel_blks_base <- relation_blocks(sc$rel_mat, sc$lb, sc$ub, grid)
    if (!is.null(sc$rel_list)) rel_blks_base <- c(rel_blks_base, do.call(c, lapply(sc$rel_list, \(info) relation_blocks(info$mat, info$lb, info$ub, grid))))
    if (!is.null(sc$idx))      rel_blks_base <- c(rel_blks_base, event_blocks_from_idx(sc$idx, sc$lb, sc$ub, grid))
    if (!is.null(sc$idx_list)) for (info in sc$idx_list) rel_blks_base <- c(rel_blks_base, event_blocks_from_idx(info$idx, info$lb, info$ub, grid))
    rel_blks <- c(list(), rel_blks_base)
    if (!is.null(sc$band_k)) rel_blks <- c(rel_blks, event_blocks_from_idx(band_idx(grid, m, sc$band_k), lb=1, ub=NULL, grid))
    for (cname in at) {
      add <- switch(cname,
                    exp  = list(mat=mat_exp, dir=rep("==", nrow(mat_exp)), rhs=b_exp),
                    obs  = list(mat=mat_obs, dir=rep("==", nrow(mat_obs)), rhs=b_obs),
                    both = list(mat=rbind(mat_exp,mat_obs), dir=rep("==", nrow(mat_exp)+nrow(mat_obs)), rhs=c(b_exp,b_obs))
      )
      cmp <- compile_blocks(c(base_blocks, rel_blks, list(marg=add)))
      sol <- run_lp_safe(numeric(ncol(cmp$A)), cmp$A, cmp$dir, cmp$rhs, maximise=FALSE)
      if (is.null(sol$status) || sol$status!=0) return(FALSE)
    }
  }
  TRUE
}
is_sample_feasible_exp  <- function(b_exp)       feasibility_core(b_exp=b_exp, b_obs=NULL, apply_to="exp")
is_sample_feasible_obs  <- function(b_obs)       feasibility_core(b_exp=NULL,  b_obs=b_obs, apply_to="obs")
is_sample_feasible_both <- function(b_exp,b_obs) feasibility_core(b_exp=b_exp, b_obs=b_obs, apply_to="both")
is_pair_feasible_both <- function(b_exp,b_obs) is_sample_feasible_both(b_exp,b_obs)

#──────────────────────── 8. サンプリング・バンク ────────────────#
.bank_key_exp <- function(Nexp) sprintf("Nexp=%d", as.integer(Nexp))
.bank_key_obs <- function(Nobs) sprintf("Nobs=%d", as.integer(Nobs))
get_sampling_bank_exp <- function(Nexp) { `0909revised_SAMPLING_BANK_EXP`[[.bank_key_exp(Nexp)]] }
get_sampling_bank_obs <- function(Nobs) { `0909revised_SAMPLING_BANK_OBS`[[.bank_key_obs(Nobs)]] }

ensure_sampling_bank_exp <- function(Nexp, M, workers=1, pb=NULL) {
  key  <- .bank_key_exp(as.integer(Nexp))
  bank <- `0909revised_SAMPLING_BANK_EXP`[[key]]
  have <- if (!is.null(bank)) length(bank$samples) else 0L
  need <- max(0L, as.integer(M) - have)
  if (need == 0L) {
    cat(sprintf("[sampling:exp] reuse Nexp=%d | bank has=%d (target M=%d)\n",
                as.integer(Nexp), have, as.integer(M)))
    return(bank)
  }
  cat(sprintf("[sampling:exp] start Nexp=%d | need=%d (have=%d)\n", as.integer(Nexp), need, have))
  Zloc <- Z; samples_new <- vector("list", need)
  gen_one <- function() {
    tries <- 0L
    repeat {
      tries <- tries + 1L
      idx <- sample.int(Zloc, size=as.integer(Nexp), replace=TRUE, prob=po_prob)
      pY_list_i <- lapply(seq_len(m), function(k) {
        yk <- grid[[paste0("Y", k)]][idx]
        as.numeric(table(factor(yk, levels=seq_len(n)))) / as.integer(Nexp)
      })
      b_exp_i <- unlist(pY_list_i); names(b_exp_i) <- names(idx_exp)
      if (is_sample_feasible_exp(b_exp_i)) return(list(pY_list=pY_list_i, tries=tries))
    }
  }
  if (workers > 1) {
    samples_new <- future.apply::future_lapply(seq_len(need), function(r) gen_one(), future.seed=TRUE, future.stdout=NA)
    for (i in seq_len(need)) pb_tick_safe(pb, tokens=list(phase="sampling-exp", obj="-", Nexp=as.integer(Nexp), Nobs=NA_integer_, r=have+i, M=as.integer(M), tries=samples_new[[i]]$tries, sumtries=sum(vapply(samples_new[seq_len(i)], function(s) s$tries, integer(1)))))
  } else {
    sumtries <- 0L
    for (r in seq_len(need)) {
      s <- gen_one(); sumtries <- sumtries + s$tries; samples_new[[r]] <- s
      pb_tick_safe(pb, tokens=list(phase="sampling-exp", obj="-", Nexp=as.integer(Nexp), Nobs=NA_integer_, r=have+r, M=as.integer(M), tries=s$tries, sumtries=sumtries))
    }
  }
  all_samples <- if (have > 0L) c(bank$samples, samples_new) else samples_new
  bank <- list(samples=all_samples)
  `0909revised_SAMPLING_BANK_EXP`[[key]] <<- bank
  SAMPLING_BANK_EXP_0909revised <<- `0909revised_SAMPLING_BANK_EXP`
  cat(sprintf("[sampling:exp] done Nexp=%d | bank %d -> %d\n", as.integer(Nexp), have, length(all_samples)))
  bank
}
ensure_sampling_bank_obs <- function(Nobs, M, workers=1, pb=NULL) {
  key  <- .bank_key_obs(as.integer(Nobs))
  bank <- `0909revised_SAMPLING_BANK_OBS`[[key]]
  have <- if (!is.null(bank)) length(bank$samples) else 0L
  need <- max(0L, as.integer(M) - have)
  if (need == 0L) {
    cat(sprintf("[sampling:obs] reuse Nexp=%d | bank has=%d (target M=%d)\n",
                as.integer(Nobs), have, as.integer(M)))
    return(bank)
  }
  cat(sprintf("[sampling:obs] start Nobs=%d | need=%d (have=%d)\n", as.integer(Nobs), need, have))
  Zloc <- Z; samples_new <- vector("list", need)
  gen_one <- function() {
    tries <- 0L
    repeat {
      tries <- tries + 1L
      idx <- sample.int(Zloc, size=as.integer(Nobs), replace=TRUE, prob=po_prob)
      tab_xy <- table(factor(grid$X[idx], levels=seq_len(m)), factor(grid$Y[idx], levels=seq_len(n)))
      pXY_i  <- as.vector(t(tab_xy)) / as.integer(Nobs)
      b_obs_i <- pXY_i; names(b_obs_i) <- names(idx_obs)
      if (is_sample_feasible_obs(b_obs_i)) return(list(pXY=pXY_i, tries=tries))
    }
  }
  if (workers > 1) {
    samples_new <- future.apply::future_lapply(seq_len(need), function(r) gen_one(), future.seed=TRUE, future.stdout=NA)
    for (i in seq_len(need)) pb_tick_safe(pb, tokens=list(phase="sampling-obs", obj="-", Nexp=NA_integer_, Nobs=as.integer(Nobs), r=have+i, M=as.integer(M), tries=samples_new[[i]]$tries, sumtries=sum(vapply(samples_new[seq_len(i)], function(s) s$tries, integer(1)))))
  } else {
    sumtries <- 0L
    for (r in seq_len(need)) {
      s <- gen_one(); sumtries <- sumtries + s$tries; samples_new[[r]] <- s
      pb_tick_safe(pb, tokens=list(phase="sampling-obs", obj="-", Nexp=NA_integer_, Nobs=as.integer(Nobs), r=have+r, M=as.integer(M), tries=s$tries, sumtries=sumtries))
    }
  }
  all_samples <- if (have > 0L) c(bank$samples, samples_new) else samples_new
  bank <- list(samples=all_samples)
  `0909revised_SAMPLING_BANK_OBS`[[key]] <<- bank
  SAMPLING_BANK_OBS_0909revised <<- `0909revised_SAMPLING_BANK_OBS`
  cat(sprintf("[sampling:obs] done Nobs=%d | bank %d -> %d\n", as.integer(Nobs), have, length(all_samples)))
  bank
}

#──────────────────────── 9. 共通ペアの準備と測時 ───────────────#
.common_key <- function(Nexp, Nobs, M) sprintf("Nexp=%d|Nobs=%d|M=%d", as.integer(Nexp), as.integer(Nobs), as.integer(M))

.make_pairs_from_banks <- function(bankE, bankO, need_M) {
  usedE <- rep(FALSE, length(bankE$samples)); usedO <- rep(FALSE, length(bankO$samples))
  pairs <- vector("list", 0L)
  for (ie in which(!usedE)) {
    b_exp_i <- unlist(bankE$samples[[ie]]$pY_list); names(b_exp_i) <- names(idx_exp)
    for (io in which(!usedO)) {
      b_obs_i <- bankO$samples[[io]]$pXY; names(b_obs_i) <- names(idx_obs)
      if (is_pair_feasible_both(b_exp_i, b_obs_i)) {
        pairs[[length(pairs)+1L]] <- list(ie=ie, io=io); usedE[ie] <- TRUE; usedO[io] <- TRUE
        if (length(pairs) >= need_M) return(pairs)
        break
      }
    }
  }
  pairs
}

.append_sampling_time_row <- function(store_name, phase, Nexp = NA_integer_, Nobs = NA_integer_,
                                      need, have_before, have_after, workers,
                                      elapsed_ms, tries_vec = numeric(0)) {
  # --- 追加: NA/NaN/Inf を除去 ---
  tries_vec <- tries_vec[is.finite(tries_vec) & !is.na(tries_vec)]
  
  existing <- if (exists(store_name, envir = .GlobalEnv)) get(store_name, envir = .GlobalEnv) else list()
  df <- existing[["log"]]
  
  row <- data.frame(
    phase         = as.character(phase),
    N_exp         = as.integer(Nexp),
    N_obs         = as.integer(Nobs),
    need          = as.integer(need),
    have_before   = as.integer(have_before),
    have_after    = as.integer(have_after),
    workers       = as.integer(workers),
    elapsed_ms    = as.numeric(elapsed_ms),
    per_accept_ms = if (is.finite(need) && need > 0) as.numeric(elapsed_ms) / as.integer(need) else NA_real_,
    tries_min     = if (length(tries_vec)) min(tries_vec, na.rm = TRUE) else NA_real_,
    tries_q25     = if (length(tries_vec)) as.numeric(stats::quantile(tries_vec, 0.25, names = FALSE, na.rm = TRUE)) else NA_real_,
    tries_median  = if (length(tries_vec)) stats::median(tries_vec, na.rm = TRUE) else NA_real_,
    tries_mean    = if (length(tries_vec)) mean(tries_vec, na.rm = TRUE) else NA_real_,
    tries_q75     = if (length(tries_vec)) as.numeric(stats::quantile(tries_vec, 0.75, names = FALSE, na.rm = TRUE)) else NA_real_,
    tries_max     = if (length(tries_vec)) max(tries_vec, na.rm = TRUE) else NA_real_,
    tries_sum     = if (length(tries_vec)) sum(tries_vec, na.rm = TRUE) else NA_real_,
    timestamp     = Sys.time(),
    stringsAsFactors = FALSE
  )
  
  df <- dplyr::bind_rows(df, row)
  existing[["log"]] <- df
  assign(store_name, existing, envir = .GlobalEnv)
  invisible(TRUE)
}

.new_tries <- function(bank, old_have) {
  if (is.null(bank)) return(numeric(0))
  total <- length(bank$samples)
  if (!is.finite(old_have) || total <= old_have) return(numeric(0))
  vapply(bank$samples[(old_have + 1):total],
         function(s) s$tries %||% NA_integer_, integer(1))
}



ensure_common_pairs <- function(Nexp, Nobs, M, workers=1, pb=NULL, times_store_name=.RESULT_SINKS$sampling) {
  key <- .common_key(Nexp, Nobs, M)
  COMMON <- get("0909revised_COMMON_PAIRS", envir=.GlobalEnv)
  if (!is.null(COMMON[[key]])) return(COMMON[[key]])
  
  # EXP bank
  bankE <- get_sampling_bank_exp(Nexp); haveE <- if (is.null(bankE)) 0L else length(bankE$samples)
  needE <- max(0L, as.integer(M) - haveE)
  t0 <- Sys.time(); bankE <- ensure_sampling_bank_exp(Nexp, M, workers=workers, pb=pb)
  t_ms <- as.numeric(difftime(Sys.time(), t0, units="secs"))*1000
  .append_sampling_time_row(times_store_name, "sampling-exp", Nexp=Nexp, need=needE,
                            have_before=haveE, have_after=length(bankE$samples), workers=workers,
                            elapsed_ms=t_ms,
                            tries_vec = .new_tries(bankE, haveE)
  )
  # OBS bank
  bankO <- get_sampling_bank_obs(Nobs); haveO <- if (is.null(bankO)) 0L else length(bankO$samples)
  needO <- max(0L, as.integer(M) - haveO)
  t0 <- Sys.time(); bankO <- ensure_sampling_bank_obs(Nobs, M, workers=workers, pb=pb)
  t_ms <- as.numeric(difftime(Sys.time(), t0, units="secs"))*1000
  .append_sampling_time_row(times_store_name, "sampling-obs", Nobs=Nobs, need=needO,
                            have_before=haveO, have_after=length(bankO$samples), workers=workers,
                            elapsed_ms=t_ms,
                            tries_vec = .new_tries(bankO, haveO)
  )
  # Pairing
  pairs <- list(); t_pair_sum <- 0
  repeat {
    t0 <- Sys.time(); more <- .make_pairs_from_banks(bankE, bankO, need_M=as.integer(M))
    t_pair_sum <- t_pair_sum + as.numeric(difftime(Sys.time(), t0, units="secs"))*1000
    pairs <- more; if (length(pairs) >= as.integer(M)) break
    need_more <- as.integer(M) - length(pairs)
    # expand EXP
    haveE <- length(bankE$samples); t0 <- Sys.time()
    bankE <- ensure_sampling_bank_exp(Nexp, haveE + need_more, workers=workers, pb=pb)
    t_ms <- as.numeric(difftime(Sys.time(), t0, units="secs"))*1000
    .append_sampling_time_row(times_store_name, "sampling-exp", Nexp=Nexp, need=need_more,
                              have_before=haveE, have_after=length(bankE$samples), workers=workers,
                              elapsed_ms=t_ms,
                              tries_vec = .new_tries(bankE, haveE)
    )
    # expand OBS
    haveO <- length(bankO$samples); t0 <- Sys.time()
    bankO <- ensure_sampling_bank_obs(Nobs, haveO + need_more, workers=workers, pb=pb)
    t_ms <- as.numeric(difftime(Sys.time(), t0, units="secs"))*1000
    .append_sampling_time_row(times_store_name, "sampling-obs", Nobs=Nobs, need=need_more,
                              have_before=haveO, have_after=length(bankO$samples), workers=workers,
                              elapsed_ms=t_ms,
                              tries_vec = .new_tries(bankO, haveO)
    )
  }
  .append_sampling_time_row(times_store_name, "pairing-both", Nexp=Nexp, Nobs=Nobs, need=as.integer(M),
                            have_before=NA_integer_, have_after=NA_integer_, workers=workers,
                            elapsed_ms=t_pair_sum, tries_vec=numeric(0))
  info <- list(pairs=pairs, bankE_key=.bank_key_exp(as.integer(Nexp)), bankO_key=.bank_key_obs(as.integer(Nobs)))
  COMMON[[key]] <- info; assign("0909revised_COMMON_PAIRS", COMMON, envir=.GlobalEnv); info
}
get_common_pairs <- function(Nexp, Nobs, M, workers=1, pb=NULL){
  key <- .common_key(Nexp,Nobs,M); COMMON <- get("0909revised_COMMON_PAIRS", envir=.GlobalEnv)
  if (!is.null(COMMON[[key]])) return(COMMON[[key]])
  ensure_common_pairs(Nexp, Nobs, M, workers=workers, pb=pb)
}

#──────────────────────── 10. 実行タイミング計測 ────────────────#
.append_time_row_scncase <- function(store_name, obj_name, scenario, case, Nexp, Nobs, M, rep, elapsed_ms) {
  existing <- if (exists(store_name, envir=.GlobalEnv)) get(store_name, envir=.GlobalEnv) else list()
  keyNexp <- sprintf("Nexp=%d", as.integer(Nexp)); keyNobs <- sprintf("Nobs=%d", as.integer(Nobs)); M_key <- sprintf("M=%d", as.integer(M))
  if (is.null(existing[[obj_name]])) existing[[obj_name]] <- list()
  if (is.null(existing[[obj_name]][[keyNexp]])) existing[[obj_name]][[keyNexp]] <- list()
  if (is.null(existing[[obj_name]][[keyNexp]][[keyNobs]])) existing[[obj_name]][[keyNexp]][[keyNobs]] <- list()
  df <- existing[[obj_name]][[keyNexp]][[keyNobs]][[M_key]]
  row <- data.frame(rep=as.integer(rep), scenario=as.character(scenario), case=as.character(case),
                    elapsed_ms=as.numeric(elapsed_ms), N_exp=as.integer(Nexp), N_obs=as.integer(Nobs), M=as.integer(M),
                    stringsAsFactors=FALSE)
  df <- if (is.null(df)) row else dplyr::bind_rows(df, row)
  existing[[obj_name]][[keyNexp]][[keyNobs]][[M_key]] <- df; assign(store_name, existing, envir=.GlobalEnv); invisible(TRUE)
}

TIMING_REPS <- getOption("lp.timing.reps", 50L)
.time_solve_ms <- function(obj_vec, cmp, reps=TIMING_REPS) {
  invisible(run_lp_safe(obj_vec, cmp$A, cmp$dir, cmp$rhs, FALSE))
  invisible(run_lp_safe(obj_vec, cmp$A, cmp$dir, cmp$rhs, TRUE))
  t0 <- proc.time()
  for(i in seq_len(reps)) {
    invisible(run_lp_safe(obj_vec, cmp$A, cmp$dir, cmp$rhs, FALSE))
    invisible(run_lp_safe(obj_vec, cmp$A, cmp$dir, cmp$rhs, TRUE))
  }
  as.numeric((proc.time() - t0)[["elapsed"]]) * 1000 / reps
}

run_for_obj_timing <- function(obj_spec, spec_name, times_store_name, N_exp, N_obs, M, rep_idx) {
  obj <- make_obj(obj_spec, grid)
  has_exp <- exists("pY_list") && is.list(pY_list) && length(pY_list)==m
  has_obs <- exists("pXY")     && is.numeric(pXY)  && length(pXY)==m*n
  cases <- character(); if (has_exp) cases <- c(cases,"exp"); if (has_obs) cases <- c(cases,"obs"); if (has_exp && has_obs) cases <- c(cases,"both")
  if (has_exp) { b_exp <- unlist(pY_list); names(b_exp) <- names(idx_exp) }
  if (has_obs) { b_obs <- pXY;             names(b_obs) <- names(idx_obs) }
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
                    exp  = list(mat=mat_exp, dir=rep("==",nrow(mat_exp)), rhs=b_exp),
                    obs  = list(mat=mat_obs, dir=rep("==",nrow(mat_obs)), rhs=b_obs),
                    both = list(mat=rbind(mat_exp,mat_obs), dir=rep("==", nrow(mat_exp)+nrow(mat_obs)), rhs=c(b_exp,b_obs))
      )
      rel_blks <- c(list(), rel_blks_base)
      if (!is.null(sc$band_k)) rel_blks <- c(rel_blks, event_blocks_from_idx(band_idx(grid, m, sc$band_k), lb=1, ub=NULL, grid))
      cmp <- compile_blocks(c(base_blocks, rel_blks, list(marg=add)))
      elapsed_ms <- .time_solve_ms(obj$obj_vec, cmp)                 # min/maxの双方を内部で実行
      .append_time_row_scncase(times_store_name, spec_name, sname, cname, N_exp, N_obs, M, rep_idx, elapsed_ms)
    }
  }
  invisible(TRUE)
}

#──────────────────────── 11. 走らせる（共通ペア→最適化） ──────────#
make_master_bar <- function(total_steps) {
  progress::progress_bar$new(
    format="[:bar] :percent | :current/:total | :elapsed | ETA: :eta | :phase :obj r=:r/:M Nexp=:Nexp Nobs=:Nobs tries=:tries Σ=:sumtries",
    total=as.integer(ifelse(is.finite(total_steps) && total_steps>0, total_steps, 1L)), clear=FALSE, width=90
  )
}

add_runs_timing <- function(obj_specs, N_exp_values, N_obs_values, M, workers=1, times_store_name=.RESULT_SINKS$times) {
  stopifnot(length(N_exp_values) == length(N_obs_values))
  pb <- make_master_bar(total_steps = sum(M * length(obj_specs) * length(N_exp_values)))
  COMMONS <- vector("list", length(N_exp_values))
  for (i in seq_along(N_exp_values)) {
    Nexp <- as.integer(N_exp_values[i]); Nobs <- as.integer(N_obs_values[i])
    COMMONS[[i]] <- ensure_common_pairs(Nexp, Nobs, M, workers=workers, pb=pb)
  }
  for (obj_name in names(obj_specs)) {
    for (i in seq_along(N_exp_values)) {
      Nexp <- as.integer(N_exp_values[i]); Nobs <- as.integer(N_obs_values[i])
      info  <- COMMONS[[i]]
      bankE <- get_sampling_bank_exp(Nexp); bankO <- get_sampling_bank_obs(Nobs)
      stopifnot(!is.null(bankE), !is.null(bankO))
      for (r in seq_len(as.integer(M))) {
        ie <- info$pairs[[r]]$ie; io <- info$pairs[[r]]$io
        pY_list <<- bankE$samples[[ie]]$pY_list
        pXY     <<- bankO$samples[[io]]$pXY
        run_for_obj_timing(obj_spec=obj_specs[[obj_name]], spec_name=obj_name,
                           times_store_name=times_store_name, N_exp=Nexp, N_obs=Nobs, M=M, rep_idx=r)
        pb_tick_safe(pb, tokens=list(phase="opt", obj=obj_name, Nexp=Nexp, Nobs=Nobs, r=r, M=M,
                                     tries=(bankE$samples[[ie]]$tries %||% 0) + (bankO$samples[[io]]$tries %||% 0),
                                     sumtries=NA_integer_))
      }
    }
  }
  .refresh_result_aliases(); invisible(TRUE)
}

#──────────────────────── 12. TeX 出力（サンプリング時間 / LP時間） ──────────#
build_summary_allN <- function(obj_runs) {
  rows <- list()
  for (keyNexp in names(obj_runs)) {
    if (!grepl("^Nexp=", keyNexp)) next
    N_exp_val <- suppressWarnings(as.integer(sub("^Nexp=([0-9]+)$", "\\1", keyNexp)))
    node_exp  <- obj_runs[[keyNexp]]; if (!is.list(node_exp)) next
    for (keyNobs in names(node_exp)) {
      if (!grepl("^Nobs=", keyNobs)) next
      N_obs_val <- suppressWarnings(as.integer(sub("^Nobs=([0-9]+)$", "\\1", keyNobs)))
      node_obs  <- node_exp[[keyNobs]]; if (!is.list(node_obs)) next
      for (Mk in names(node_obs)) {
        if (!grepl("^M=", Mk)) next
        res <- node_obs[[Mk]]; if (is.null(res) || is.null(res$summary)) next
        sm <- res$summary; sm$N_exp <- N_exp_val; sm$N_obs <- N_obs_val; sm$N <- if (!is.na(N_obs_val)) N_obs_val else N_exp_val
        sm$M <- suppressWarnings(as.integer(sub("^M=([0-9]+)$", "\\1", Mk)))
        rows[[paste(keyNexp, keyNobs, Mk, sep=":")]] <- sm
      }
    }
  }
  if (!length(rows)) return(data.frame())
  dplyr::arrange(dplyr::bind_rows(rows), N_exp, N_obs, M, scenario, case)
}

# sampling times table
export_sampling_times_tex <- function(result_sampling, Ns=c(10,100,1000,10000), digits=0, out_dir=file.path("tex","sampling")) {
  if (!dir.exists(out_dir)) dir.create(out_dir, recursive=TRUE, showWarnings=FALSE)
  logdf <- result_sampling[["log"]]; if (is.null(logdf) || !nrow(logdf)) return(invisible(FALSE))
  logdf$N <- dplyr::coalesce(logdf$N_exp, logdf$N_obs)
  get_med <- function(N, phase){ x <- logdf[logdf$N==N & logdf$phase==phase, "elapsed_ms", drop=TRUE]; if (!length(x)) return(NA_real_); stats::median(x, na.rm=TRUE) }
  hdrNs <- paste(sprintf("$N=%s$", Ns), collapse=" & ")
  lines <- character()
  for (rowname in c("Exp sampling (ms)"="sampling-exp","Obs sampling (ms)"="sampling-obs","Pairing (ms)"="pairing-both","Total (ms)"="__total__")) {
    cells <- character(length(Ns))
    for (j in seq_along(Ns)) {
      N <- Ns[j]
      cells[j] <- if (rowname=="__total__") {
        sE <- get_med(N,"sampling-exp"); sO <- get_med(N,"sampling-obs"); sP <- get_med(N,"pairing-both"); .fmt_num(sum(sE,sO,sP,na.rm=TRUE), digits)
      } else .fmt_num(get_med(N, rowname), digits)
    }
    label <- if (rowname=="__total__") "Total (ms)" else names(rowname)
    lines <- c(lines, paste(label, paste(cells, collapse=" & "), sep=" & "))
  }
  tex <- paste0("\\begin{tabular}{l|", paste(rep("c", length(Ns)), collapse=""), "}\n\\hline\nMetric & ", hdrNs, " \\\\\n\\hline\\hline\n",
                paste(lines, collapse=" \\\\\n"), " \\\\\n\\hline\n\\end{tabular}\n")
  writeLines(tex, file.path(out_dir, "sampling_times.tex"), useBytes=TRUE); invisible(TRUE)
}

# LP時間（case別）の中央値テーブル
export_table_times_by_case <- function(result_times, obj_name, case_name=c("exp","obs","both"),
                                       Ns=c(10,100,1000,10000), digits=0, out_dir=file.path("tex","times")) {
  .dir_ensure <- function(p){ if(!dir.exists(p)) dir.create(p, recursive=TRUE, showWarnings=FALSE); p }
  .dir_ensure(out_dir); case_name <- match.arg(case_name)
  node <- result_times[[obj_name]]; if (is.null(node)) return(invisible(FALSE))
  scen_order <- names(constraint_scenarios)
  get_df_for_N <- function(N){
    keyNexp <- sprintf("Nexp=%d", as.integer(N)); keyNobs <- sprintf("Nobs=%d", as.integer(N))
    sub <- node[[keyNexp]][[keyNobs]]; if (is.null(sub)) return(NULL)
    Mkeys <- names(sub); Mkeys <- Mkeys[grepl("^M=", Mkeys)]; if (!length(Mkeys)) return(NULL)
    df <- sub[[Mkeys[1]]]; if (is.null(df) || !nrow(df)) return(NULL)
    df <- df[df$case == case_name, , drop=FALSE]; if (!nrow(df)) return(NULL)
    df |>
      dplyr::group_by(scenario) |>
      dplyr::summarise(med=stats::median(elapsed_ms, na.rm=TRUE), .groups="drop")
  }
  perN <- lapply(Ns, get_df_for_N); has_any <- Reduce(`||`, lapply(perN, function(d) !is.null(d) && nrow(d)>0), init=FALSE)
  if (!has_any) return(invisible(FALSE))
  lines <- character(); fmt <- function(x) if (is.na(x)||length(x)==0) "" else sprintf(paste0("%.",digits,"f"), x)
  for (sc in scen_order) {
    cells <- character(length(Ns))
    for (j in seq_along(Ns)) {
      dj <- perN[[j]]
      cells[j] <- if (!is.null(dj) && sc %in% dj$scenario) fmt(dj$med[dj$scenario==sc]) else ""
    }
    lines <- c(lines, paste(sc, paste(cells, collapse=" & "), sep=" & "))
  }
  hdrNs <- paste(sprintf("$N=%s$", Ns), collapse=" & ")
  tex <- paste0("\\begin{tabular}{l|", paste(rep("c", length(Ns)), collapse=""), "}\n",
                "\\hline\nScenario (case=", case_name, ") & ", hdrNs, " \\\\\n\\hline\\hline\n",
                paste(lines, collapse=" \\\\\n"), " \\\\\n\\hline\n\\end{tabular}\n")
  base <- gsub("[^A-Za-z0-9_]+","_", paste0("TIME_", obj_name, "_", case_name))
  writeLines(tex, file.path(out_dir, sprintf("%s.tex", base)), useBytes=TRUE); invisible(TRUE)
}

#──────────────────────── 13. 実行スクリプト（末尾） ──────────────#
# 並列プラン
workers <- max(1, parallel::detectCores() - 2)
future::plan(future::multisession, workers = workers)

# N・M 等
N_exp_values <- c(10, 100, 1000, 10000)
N_obs_values <- c(10, 100, 1000, 10000)
M <- 1
options(lp.timing.reps = 100L)   # ← K をここで指定（K=1 等も可）

# 1) 共通サンプルで最適化を実行（所要時間ログ）
add_runs_timing(obj_specs, N_exp_values, N_obs_values, M, workers,
                times_store_name = "0909revised_RESULT_times")

# 2) サンプリング＋ペアリング時間を TeX 出力（tex/sampling/sampling_times.tex）
export_sampling_times_tex(RESULT_sampling_times_0909revised,
                          Ns = c(10,100,1000,10000),
                          digits = 0,
                          out_dir = file.path("tex","sampling"))

# 3) LP時間（例：bothケース）の中央値テーブルを TeX 出力
export_table_times_by_case(`0909revised_RESULT_times`,
                           obj_name  = "P(Y0=0,Y1=0,Y2=1)",
                           case_name = "both",
                           Ns        = c(10,100,1000,10000),
                           digits    = 0,
                           out_dir   = file.path("tex","times"))

# 後片付け
future::plan(sequential); invisible(gc())

for(ob in names(obj_specs)){
  for (cs in c("exp","obs","both")) {
  export_table_times_by_case(`0909revised_RESULT_times`,
                             obj_name=ob,
                             case_name=cs,
                             Ns=c(10,100,1000,10000),
                             digits=0,
                             out_dir=file.path("tex","times")
                             )
}
}







# ───────────────── コンパクト版：ケース別タイム表（あなたの希望の体裁） ────────────────
export_table_times_by_case_compact <- function(result_times,
                                               obj_name,
                                               case_name = c("exp","obs","both"),
                                               Ns = c(10,100,1000,10000),
                                               digits = 0,
                                               out_dir = file.path("tex","times")) {
  .dir_ensure <- function(p){ if(!dir.exists(p)) dir.create(p, recursive=TRUE, showWarnings=FALSE); p }
  .dir_ensure(out_dir)
  case_name <- match.arg(case_name)
  node <- result_times[[obj_name]]
  if (is.null(node)) return(invisible(FALSE))
  
  # Nごとの（その目的関数の）rep全体から、指定caseの scenario別・median(ms)
  get_df_for_N <- function(N){
    keyNexp <- sprintf("Nexp=%d", as.integer(N))
    keyNobs <- sprintf("Nobs=%d", as.integer(N))
    sub <- node[[keyNexp]][[keyNobs]]
    if (is.null(sub)) return(NULL)
    Mkeys <- names(sub); Mkeys <- Mkeys[grepl("^M=", Mkeys)]
    if (!length(Mkeys)) return(NULL)
    df <- sub[[Mkeys[1]]]
    if (is.null(df) || !nrow(df)) return(NULL)
    df <- df[df$case == case_name, , drop=FALSE]
    if (!nrow(df)) return(NULL)
    df |>
      dplyr::group_by(scenario) |>
      dplyr::summarise(med = stats::median(elapsed_ms, na.rm = TRUE), .groups="drop")
  }
  
  # 表示順： (i) none, (ii) Y0<=Y1, (iii) Y1<=Y2, (iv) Y0<=Y1<=Y2
  scen_order <- c("none","Y0<=Y1 a.s.","Y1<=Y2 a.s.","Y0<=Y1<=Y2 a.s.")
  # ラベル（(i)〜(iv)）
  label_assumption <- function(key){
    switch(tolower(key),
           "none"          = "(i)",
           "y0<=y1"        = "(ii)",
           "y1<=y2"        = "(iii)",
           "y0<=y1<=y2"    = "(iv)",
           "(?)"
    )
  }
  # 正規化キー
  .scen_key <- function(s){
    s0 <- tolower(gsub("\\s+","", s))
    s0 <- gsub("\\.a\\.s\\.|a\\.s\\.|a\\.?s\\.?","", s0)
    s0 <- gsub("≤","<=", s0, fixed=TRUE)
    s0 <- gsub("leq","<=", s0, fixed=TRUE)
    s0 <- gsub("<=+","<=", s0)
    s0 <- sub("^y0<=y1<=y2$","y0<=y1<=y2", s0)
    s0
  }
  # Nごとの集計を用意
  perN <- lapply(Ns, get_df_for_N)
  has_any <- Reduce(`||`, lapply(perN, function(d) !is.null(d) && nrow(d)>0), init = FALSE)
  if (!has_any) return(invisible(FALSE))
  
  # colspec（Assump. 1列 + N列）
  colspec <- paste0("{c|", paste(rep("c", length(Ns)), collapse=""), "}")
  hdrNs   <- paste(sprintf("$N=%s$", Ns), collapse=" & ")
  
  # 行を組み立て
  .fmt <- function(x) if (is.na(x) || length(x)==0) "" else sprintf(paste0("%.", digits, "f"), x)
  lines <- character()
  for (sc in scen_order) {
    key_norm <- .scen_key(sc)
    label <- switch(key_norm,
                    "none"         = "(i)",
                    "y0<=y1"       = "(ii)",
                    "y1<=y2"       = "(iii)",
                    "y0<=y1<=y2"   = "(iv)",
                    "(?)"
    )
    cells <- character(length(Ns))
    for (j in seq_along(Ns)) {
      dj <- perN[[j]]
      if (!is.null(dj)) {
        # dj$scenario は生値なので正規化比較
        rows <- which(vapply(dj$scenario, .scen_key, "") == key_norm)
        cells[j] <- if (length(rows)) .fmt(dj$med[rows[1]]) else ""
      } else {
        cells[j] <- ""
      }
    }
    lines <- c(lines, paste(label, paste(cells, collapse=" & "), sep=" & "))
  }
  
  # タイトル（例：Both / Exp / Obs）
  ttl <- switch(case_name, exp="Exp", obs="Obs", both="Both", case_name)
  
  tex <- paste0(
    "\\begin{tabular}", colspec, "\n",
    "    \\multicolumn{", 1 + length(Ns), "}{c}{", ttl, "}\\\\\n",
    "    \\hline\n",
    "    Assump. & ", hdrNs, " \\\\\n",
    "    \\hline\\hline\n",
    "    ", paste(lines, collapse=" \\\\\n    "), " \\\\\n",
    "    \\hline\n",
    "\\end{tabular}\n"
  )
  
  # 出力ファイル名
  .filename_from_obj <- function(s){
    s <- gsub("\\s+", "", s)
    s <- gsub("\\[", "(", s); s <- gsub("\\]", ")", s)
    s <- gsub("\\|", "_", s); s <- gsub("/|\\\\", "_", s)
    s <- gsub("[:*?\"<>]", "_", s)
    s
  }
  base <- .filename_from_obj(paste0("TIME_COMPACT_", obj_name, "_", case_name))
  writeLines(tex, file.path(out_dir, sprintf("%s.tex", base)), useBytes=TRUE)
  invisible(TRUE)
}


for (obj_name in names(RESULT_times_0909revised)) {
  # 目的関数ノードだけ（サマリ以外）を対象にする場合は必要に応じてフィルタ
  for (cs in c("exp","obs","both")) {
    export_table_times_by_case_compact(
      RESULT_times_0909revised,
      obj_name  = obj_name,
      case_name = cs,
      Ns        = c(10,100,1000,10000),
      digits    = 0,
      out_dir   = file.path("tex","times")
    )
  }
}

