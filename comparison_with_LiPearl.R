# =========================
# 0) Libraries
# =========================
suppressPackageStartupMessages({
  library(Matrix)
  library(Rglpk)
  library(dplyr)
  library(tidyr)
  library(purrr)
  library(tibble)
})

# =========================
# 1) Basic setup
# =========================
m <- 3  # |X| (= number of arms)
n <- 3  # |Y| (= number of outcome categories)

# グリッド（反事実ジョイントの各行を表す）
build_grid <- function(m, n){
  Y_list <- setNames(lapply(seq_len(m), \(.) seq_len(n)), paste0("Y", seq_len(m)))
  do.call(expand.grid, c(Y_list, list(X=seq_len(m)), list(Y=seq_len(n))))
}

# 一貫性 (consistency) 違反の行インデックス：割当 X のとき観測 Y が対応する潜在 Y_X でない
consistency_bad <- function(grid, m){
  Y_cols <- paste0("Y", seq_len(m))
  Y_mat  <- as.matrix(grid[, Y_cols])
  picked <- Y_mat[cbind(seq_len(nrow(grid)), as.integer(grid$X))]
  which(picked != grid$Y)
}

# （任意）単調性（非減少）違反の行インデックス
monotonicity_bad <- function(grid, m){
  Y_cols <- paste0("Y", seq_len(m))
  Y_mat  <- as.matrix(grid[, Y_cols])
  which(apply(Y_mat, 1, function(v) any(diff(v) < 0)))
}

grid <- build_grid(m, n)  # 反事実ジョイントの全行

# =========================
# 2) Random truth generators（ここが A/B/C の選択肢）
# =========================
# A: a_xy (= P(X,Y)) を保ったまま、各 (X,Y) セルの内部でランダムに割付（Dirichlet）
#    row_weight は長さ Z のベクトル or function(row)→weight
make_true_joint_random_from_a_xy <- function(
    a_xy, grid, m, n, alpha = 1, enforce_monotone = FALSE, row_weight = NULL
){
  a_xy <- a_xy / sum(a_xy)
  Z <- nrow(grid)
  bad <- consistency_bad(grid, m)
  if (enforce_monotone) bad <- union(bad, monotonicity_bad(grid, m))
  
  # 行ごとの重み
  if (is.null(row_weight)) {
    w_row <- rep(1, Z)
  } else if (is.function(row_weight)) {
    w_row <- vapply(seq_len(Z), function(i) row_weight(grid[i, , drop=FALSE]), numeric(1))
  } else {
    stopifnot(length(row_weight) == Z); w_row <- as.numeric(row_weight)
  }
  
  p <- numeric(Z)
  for (x in seq_len(m)) for (y in seq_len(n)) {
    idx <- which(grid$X == x & grid$Y == y)
    idx <- setdiff(idx, bad)   # 許容行のみ
    if (!length(idx)) {
      if (a_xy[x,y] == 0) next
      stop(sprintf("No admissible rows for (X=%d,Y=%d) but a_xy>0", x, y))
    }
    # Dirichlet：Gamma(shape=alpha*weight) → 正規化
    g <- rgamma(length(idx), shape = alpha * pmax(1e-12, w_row[idx]), rate = 1)
    g <- if (sum(g) > 0) g / sum(g) else rep(1/length(idx), length(idx))
    p[idx] <- p[idx] + a_xy[x,y] * g
  }
  stopifnot(abs(sum(p) - 1) < 1e-9)
  p
}

# B: a_xy 自体もランダム（Dirichlet）→ A で内部割付
make_true_joint_fully_random <- function(
    grid, m, n, alpha_xy = 1, alpha_cell = 1,
    enforce_monotone = FALSE, row_weight = NULL
){
  w_xy <- rgamma(m*n, shape = alpha_xy, rate = 1)
  a_xy <- matrix(w_xy / sum(w_xy), nrow = m, byrow = TRUE)
  p <- make_true_joint_random_from_a_xy(
    a_xy, grid, m, n, alpha = alpha_cell,
    enforce_monotone = enforce_monotone, row_weight = row_weight
  )
  list(a_xy = a_xy, po_prob_true = p)
}

# C: 全体ジョイント（consistency/monotonicity OK の行だけ）に直接ランダム割付
#    method="dirichlet" or "sampling"
make_true_joint_direct_random <- function(
    grid, m, n, method = c("dirichlet","sampling"),
    alpha = 1, N_joint_draws = 10000,
    enforce_monotone = FALSE, row_weight = NULL
){
  method <- match.arg(method)
  Z <- nrow(grid)
  bad <- consistency_bad(grid, m)
  if (enforce_monotone) bad <- union(bad, monotonicity_bad(grid, m))
  ok <- setdiff(seq_len(Z), bad)
  stopifnot(length(ok) > 0)
  
  if (is.null(row_weight)) {
    w_row <- rep(1, Z)
  } else if (is.function(row_weight)) {
    w_row <- vapply(seq_len(Z), function(i) row_weight(grid[i, , drop=FALSE]), numeric(1))
  } else {
    stopifnot(length(row_weight) == Z); w_row <- as.numeric(row_weight)
  }
  w_ok <- pmax(0, w_row[ok])
  if (sum(w_ok) == 0) w_ok <- rep(1, length(ok))
  w_ok <- w_ok / sum(w_ok)
  
  p <- numeric(Z)
  if (method == "dirichlet") {
    g <- rgamma(length(ok), shape = alpha * w_ok, rate = 1)
    g <- if (sum(g) > 0) g / sum(g) else rep(1/length(ok), length(ok))
    p[ok] <- g
  } else {
    idx <- sample(ok, size = N_joint_draws, replace = TRUE, prob = w_ok)
    tab <- table(factor(idx, levels = ok))
    p[ok] <- as.numeric(tab) / N_joint_draws
  }
  stopifnot(abs(sum(p) - 1) < 1e-9)
  p
}

# ジョイントから a_xy を復元（consistency を仮定）
compute_a_xy_from_joint <- function(po_prob_true, grid, m, n){
  a_xy <- matrix(0, nrow = m, ncol = n)
  for (x in seq_len(m)) for (y in seq_len(n)) {
    a_xy[x,y] <- sum(po_prob_true[ grid$X==x & grid$Y==y ])
  }
  a_xy
}

# =========================
# 3) Li–Pearl helpers（論文の定理に基づく境界。ロジックは変更しない）
# =========================
.clamp01 <- function(x) pmax(0, pmin(1, x))
# 以降は pY_list / pXY（ベクトル）をグローバル参照
.get_pyx <- function(i, j, m, n) pY_list[[j]][i]
.get_pxy <- function(j, i, m, n) pXY[(j-1)*n + i]
.get_pX  <- function(j, m, n)    sum(pXY[((j-1)*n + 1):(j*n)])
.get_pY  <- function(i, m, n)    sum(pXY[seq(i, m*n, by=n)])

.bounds_yixj <- function(i, j, m, n) { v <- .get_pyx(i,j,m,n); c(lb=v, ub=v) }
.bounds_PPre1 <- function(i, j, m, n){
  pyx <- .get_pyx(i,j,m,n); pyi <- .get_pY(i,m,n); pxjyi <- .get_pxy(j,i,m,n)
  c(lb=.clamp01(max(pxjyi, pyx+pyi-1)), ub=.clamp01(min(pyx, pyi)))
}
.bounds_PSub1 <- function(i, j, kx, m, n){
  pyx <- .get_pyx(i,j,m,n); pxjyi <- .get_pxy(j,i,m,n); pxj <- .get_pX(j,m,n); pxk <- .get_pX(kx,m,n)
  c(lb=.clamp01(max(0, pyx - pxjyi - 1 + pxj + pxk)),
    ub=.clamp01(min(pyx - pxjyi, pxk)))
}
.bounds_PN1 <- function(i, j, p, q, m, n){
  pyx <- .get_pyx(i,j,m,n); pxpyq <- .get_pxy(p,q,m,n); pxj <- .get_pX(j,m,n); pxjyi <- .get_pxy(j,i,m,n)
  c(lb=.clamp01(max(0, pyx + pxpyq - 1 + pxj - pxjyi)),
    ub=.clamp01(min(pyx - pxjyi, pxpyq)))
}
.bounds_PRep1 <- function(i, j, q, m, n){
  pyx <- .get_pyx(i,j,m,n); pyq <- .get_pY(q,m,n); pxj <- .get_pX(j,m,n); pxjyi <- .get_pxy(j,i,m,n)
  term3 <- 0
  for (p in setdiff(seq_len(m), j)) term3 <- term3 + max(0, pyx + .get_pxy(p,q,m,n) - 1 + pxj - pxjyi)
  c(lb=.clamp01(max(0, pyx + pyq - 1, term3)),
    ub=.clamp01(min(pyx - pxjyi, pyq - .get_pxy(j,q,m,n))))
}
.bounds_PNSk <- function(yis, js, m, n){
  k <- length(yis); pyxs <- mapply(.get_pyx, yis, js, MoreArgs=list(m=m,n=n))
  if (k==1) return(.bounds_yixj(yis[1], js[1], m, n))
  termA <- sum(pyxs) - k + 1
  termB <- max(sapply(seq_len(k), function(t) .bounds_PNSk(yis[-t], js[-t], m, n)["lb"] + pyxs[t] - 1))
  others <- setdiff(seq_len(m), unique(js))
  sumPN  <- sum(sapply(seq_len(k), function(r) .bounds_PN_k(yis[-r], js[-r], js[r], yis[r], m, n)["lb"]))
  sumSub <- if (length(others)) sum(sapply(others, function(p) .bounds_PSub_k(yis, js, p, m, n)["lb"])) else 0
  lb <- max(0, termA, termB, sumPN + sumSub)
  termU1 <- min(pyxs)
  termU2 <- min(sapply(seq_len(k), function(t) .bounds_PNSk(yis[-t], js[-t], m, n)["ub"]))
  sumPNu <- sum(sapply(seq_len(k), function(r) .bounds_PN_k(yis[-r], js[-r], js[r], yis[r], m, n)["ub"]))
  sumSubu <- if (length(others)) sum(sapply(others, function(p) .bounds_PSub_k(yis, js, p, m, n)["ub"])) else 0
  ub <- min(termU1, termU2, sumPNu + sumSubu)
  c(lb=.clamp01(lb), ub=.clamp01(ub))
}
.bounds_PSub_k <- function(yis, js, p, m, n){
  k <- length(yis); pyxs <- mapply(.get_pyx, yis, js, MoreArgs=list(m=m,n=n))
  if (k==1) return(.bounds_PSub1(yis[1], js[1], p, m, n))
  termA <- sum(pyxs) + .get_pX(p,m,n) - k
  termB <- max(sapply(seq_len(k), function(t) .bounds_PNSk(yis[-t], js[-t], m, n)["lb"] + .bounds_PSub1(yis[t], js[t], p, m, n)["lb"] - 1))
  lb <- max(0, termA, termB)
  termU <- min(min(pyxs), .get_pX(p,m,n),
               min(sapply(seq_len(k), function(t) .bounds_PNSk(yis[-t], js[-t], m, n)["ub"])),
               min(sapply(seq_len(k), function(t) .bounds_PSub1(yis[t], js[t], p, m, n)["ub"])))
  c(lb=.clamp01(lb), ub=.clamp01(termU))
}
.bounds_PN_k <- function(yis, js, p, q, m, n){
  k <- length(yis); pyxs <- mapply(.get_pyx, yis, js, MoreArgs=list(m=m,n=n))
  if (k==1) return(.bounds_PN1(yis[1], js[1], p, q, m, n))
  termA <- sum(pyxs) + .get_pxy(p,q,m,n) - k
  termB <- max(sapply(seq_len(k), function(t) .bounds_PNSk(yis[-t], js[-t], m, n)["lb"] + .bounds_PN1(yis[t], js[t], p, q, m, n)["lb"] - 1))
  lb <- max(0, termA, termB)
  termU <- min(min(pyxs), .get_pxy(p,q,m,n),
               min(sapply(seq_len(k), function(t) .bounds_PNSk(yis[-t], js[-t], m, n)["ub"])),
               min(sapply(seq_len(k), function(t) .bounds_PN1(yis[t], js[t], p, q, m, n)["ub"])))
  c(lb=.clamp01(lb), ub=.clamp01(termU))
}
.bounds_PRep_k <- function(yis, js, q, m, n){
  k <- length(yis); pyxs <- mapply(.get_pyx, yis, js, MoreArgs=list(m=m,n=n))
  if (k==1) return(.bounds_PRep1(yis[1], js[1], q, m, n))
  termA <- sum(pyxs) + .get_pY(q,m,n) - k
  termB <- max(sapply(seq_len(k), function(t)
    .bounds_PNSk(yis[-t], js[-t], m, n)["lb"] + .bounds_PRep1(yis[t], js[t], q, m, n)["lb"] - 1))
  idx_q <- which(yis == q)
  sumPN1 <- if (length(idx_q))
    sum(sapply(idx_q, function(r) .bounds_PN_k(yis[-r], js[-r], js[r], yis[r], m, n)["lb"])) else 0
  others <- setdiff(seq_len(m), unique(js))
  sumPN2 <- if (length(others))
    sum(sapply(others, function(p) .bounds_PN_k(yis, js, p, q, m, n)["lb"])) else 0
  lb <- max(0, termA, termB, sumPN1 + sumPN2)
  termU <- min(
    min(pyxs),
    .get_pY(q,m,n),
    min(sapply(seq_len(k), function(t) .bounds_PNSk(yis[-t], js[-t], m, n)["ub"])),
    min(sapply(seq_len(k), function(t) .bounds_PRep1(yis[t], js[t], q, m, n)["ub"])),
    {
      sumPN1_u <- if (length(idx_q))
        sum(sapply(idx_q, function(r) .bounds_PN_k(yis[-r], js[-r], js[r], yis[r], m, n)["ub"])) else 0
      sumPN2_u <- if (length(others))
        sum(sapply(others, function(p) .bounds_PN_k(yis, js, p, q, m, n)["ub"])) else 0
      sumPN1_u + sumPN2_u
    }
  )
  c(lb=.clamp01(lb), ub=.clamp01(termU))
}

# joint/conditional の Li–Pearl 境界（割るべき時だけ割る）
compute_lipearl_bounds_for_obj <- function(obj_spec, m, n){
  if (!(obj_spec$type %in% c("joint","conditional"))) return(NULL)
  if (!is.null(obj_spec$target_ineq)) return(NULL)
  if (is.null(obj_spec$target_eq)) return(NULL)
  eq_idx <- which(!is.na(obj_spec$target_eq)); if (!length(eq_idx)) return(NULL)
  yis <- as.integer(obj_spec$target_eq[eq_idx]); js <- as.integer(eq_idx)
  hasX <- !is.null(obj_spec$condX); hasY <- !is.null(obj_spec$condY)
  want_cond <- identical(obj_spec$type, "conditional")
  
  # joint の Li–Pearl
  b <- if (!hasX && !hasY) {
    .bounds_PNSk(yis, js, m, n)
  } else if (hasX && !hasY) {
    .bounds_PSub_k(yis, js, p = obj_spec$condX, m, n)
  } else if (!hasX && hasY) {
    if (length(yis) == 1 && yis[1] == obj_spec$condY) .bounds_PPre1(yis[1], js[1], m, n)
    else .bounds_PRep_k(yis, js, q = obj_spec$condY, m, n)
  } else {
    .bounds_PN_k(yis, js, p = obj_spec$condX, q = obj_spec$condY, m, n)
  }
  lb <- unname(b["lb"]); ub <- unname(b["ub"])
  
  # conditional が欲しいときだけ割る
  if (want_cond) {
    denom <- if (hasX && hasY) {
      .get_pxy(obj_spec$condX, obj_spec$condY, m, n)
    } else if (hasX) {
      .get_pX(obj_spec$condX, m, n)
    } else if (hasY) {
      .get_pY(obj_spec$condY, m, n)
    } else 1
    if (!is.finite(denom) || denom <= 0) return(list(lb = NA_real_, ub = NA_real_))
    list(lb = lb/denom, ub = ub/denom)
  } else list(lb = lb, ub = ub)
}

# 自明上限のチェック（optional）
.li_joint_cap <- function(obj_spec, m, n){
  hasX <- !is.null(obj_spec$condX); hasY <- !is.null(obj_spec$condY)
  if (!hasX && !hasY) {
    eq_idx <- which(!is.na(obj_spec$target_eq))
    yis <- as.integer(obj_spec$target_eq[eq_idx]); js <- as.integer(eq_idx)
    mins <- mapply(function(i,j) .get_pyx(i,j,m,n), yis, js)
    return(min(mins))
  } else if (hasX && !hasY) {
    return(.get_pX(obj_spec$condX, m, n))
  } else if (!hasX && hasY) {
    return(.get_pY(obj_spec$condY, m, n))
  } else {
    return(.get_pxy(obj_spec$condX, obj_spec$condY, m, n))
  }
}
check_lipearl_sanity <- function(obj_spec, li_lb, li_ub, m, n){
  cap <- .li_joint_cap(obj_spec, m, n)
  if (is.finite(li_ub) && li_ub > cap + 1e-9)
    warning(sprintf("Li–Pearl UB %.6f exceeds trivial cap %.6f", li_ub, cap))
  if (is.finite(li_lb) && li_lb < -1e-12)
    warning(sprintf("Li–Pearl LB < 0 (%.6f).", li_lb))
  if (is.finite(li_lb) && is.finite(li_ub) && li_lb - li_ub > 1e-12)
    warning(sprintf("Li–Pearl LB > UB (lb=%.6f, ub=%.6f).", li_lb, li_ub))
  invisible(TRUE)
}

# =========================
# 4) Objective maker（目的ベクトル）
# =========================
make_obj <- function(obj_spec, grid){
  Z <- nrow(grid); m <- sum(grepl("^Y\\d+$", names(grid)))
  v <- rep(TRUE, Z)
  apply_conditions <- function(v, grid, conds){
    for(cond in conds){
      Yi <- grid[[paste0("Y", cond$var)]]
      v  <- v & switch(cond$op,
                       "==" = (Yi == cond$val),
                       "<"  = (Yi  < cond$val),
                       "<=" = (Yi <= cond$val),
                       ">"  = (Yi  > cond$val),
                       ">=" = (Yi >= cond$val),
                       stop("unsupported op: ", cond$op))
    }
    v
  }
  if (obj_spec$type %in% c("conditional","joint")){
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
    if (obj_spec$type == "conditional"){
      if (!is.null(obj_spec$condX) && !is.null(obj_spec$condY)) {
        denom_lab <- sprintf("obs_k%d_y%d", obj_spec$condX, obj_spec$condY)
      } else if (!is.null(obj_spec$condX)) {
        denom_lab <- sprintf("obs_k%d_yALL", obj_spec$condX) # 非使用
      } else if (!is.null(obj_spec$condY)) {
        denom_lab <- sprintf("obs_kALL_y%d", obj_spec$condY)
      }
    }
    return(list(obj_vec=obj_vec, denom_lab=denom_lab))
  }
  stop("unknown type")
}

# =========================
# 5) LP 準備
# =========================
marginal_mat <- function(idx_list, Z){
  rows <- rep(seq_along(idx_list), lengths(idx_list))
  cols <- unlist(idx_list)
  Matrix::sparseMatrix(i = rows, j = cols, x = 1, dims = c(length(idx_list), Z))
}
build_marginals <- function(grid, m, n){
  Z <- nrow(grid)
  idx_exp <- idx_obs <- vector("list", m*n)
  cnt <- 1
  for(k in seq_len(m)) for(y in seq_len(n)){
    idx_exp[[cnt]] <- which(grid[[paste0("Y",k)]] == y)
    idx_obs[[cnt]] <- which(grid$X==k & grid$Y==y)
    cnt <- cnt + 1
  }
  names(idx_obs) <- sprintf("obs_k%d_y%d", rep(seq_len(m), each=n), rep(seq_len(n), m))
  list(mat_exp=marginal_mat(idx_exp, Z), mat_obs=marginal_mat(idx_obs, Z), obs_names=names(idx_obs))
}
run_lp_safe <- function(obj, A, dir, rhs, maximise = FALSE) {
  ctrl1 <- list(canonicalize_status=TRUE, presolve=TRUE,  verbose=FALSE, tm_limit=0)
  ctrl2 <- list(canonicalize_status=TRUE, presolve=FALSE, verbose=FALSE, tm_limit=0)
  bounds <- list(lower=list(ind=seq_len(length(obj)), val=rep(0,length(obj))),
                 upper=list(ind=seq_len(length(obj)), val=rep(1,length(obj))))
  .solve <- function(ctrl) Rglpk::Rglpk_solve_LP(obj=obj, mat=A, dir=dir, rhs=rhs,
                                                 bounds=bounds, max=maximise, control=ctrl)
  sol <- .solve(ctrl1); if (!is.null(sol$status) && sol$status==0) return(sol)
  sol2 <- .solve(ctrl2); if (!is.null(sol2$status) && sol2$status==0) return(sol2)
  sol2
}

# =========================
# 6) Drivers: Oracle / Sampling
# =========================
# サンプルを介さずに「真の周辺」をそのまま使って LP と Li–Pearl を比較
run_for_obj_both_none_oracle <- function(obj_spec, grid, m, n, po_prob_true, a_xy){
  Z <- nrow(grid)
  bad_rows <- consistency_bad(grid, m)
  zero_mat <- function(idx, Z) if(length(idx)) Matrix::sparseMatrix(i=seq_along(idx), j=idx, x=1, dims=c(length(idx),Z)) else NULL
  base_blocks <- list(
    sum  = list(mat=Matrix::Matrix(1,1,Z,sparse=TRUE), dir="==", rhs=1),
    zero = list(mat=zero_mat(bad_rows,Z), dir=rep("==", length(bad_rows)), rhs=rep(0,length(bad_rows)))
  )
  mg <- build_marginals(grid, m, n)
  
  # 観測周辺（観測 joint）を厳密等式で RHS に
  pXY_true <- as.vector(t(a_xy))
  names(pXY_true) <- sprintf("obs_k%d_y%d", rep(seq_len(m), each=n), rep(seq_len(n), m))
  
  # 介入周辺（実験）を真の joint から厳密に作る
  pY_list_true <- lapply(seq_len(m), function(k) {
    vec <- numeric(n)
    for (y in seq_len(n)) vec[y] <- sum(po_prob_true[ grid[[paste0("Y",k)]] == y ])
    vec
  })
  
  # Li–Pearl 用の“グローバル”
  pXY <<- pXY_true
  pY_list <<- pY_list_true
  
  # 目的ベクトル
  obj <- make_obj(obj_spec, grid)
  
  # both×none の等式（実験と観測を厳密に）
  add <- list(
    mat = rbind(mg$mat_exp, mg$mat_obs),
    dir = rep("==", nrow(mg$mat_exp)+nrow(mg$mat_obs)),
    rhs = c(unlist(pY_list_true), as.numeric(pXY_true))
  )
  
  mats <- lapply(c(base_blocks, list(marg=add)), `[[`, "mat")
  keep <- !sapply(mats, is.null)
  A    <- do.call(rbind, mats[keep])
  dir  <- unlist(lapply(c(base_blocks, list(marg=add))[keep], `[[`, "dir"))
  rhs  <- unlist(lapply(c(base_blocks, list(marg=add))[keep], `[[`, "rhs"))
  
  # LP solve
  smin <- run_lp_safe(obj$obj_vec, A, dir, rhs, FALSE)
  smax <- run_lp_safe(obj$obj_vec, A, dir, rhs, TRUE)
  
  # Li–Pearl（オラクル周辺量で）
  li <- compute_lipearl_bounds_for_obj(obj_spec, m, n)
  li_lb <- if (is.null(li)) NA_real_ else as.numeric(li$lb)
  li_ub <- if (is.null(li)) NA_real_ else as.numeric(li$ub)
  check_lipearl_sanity(obj_spec, li_lb, li_ub, m, n)
  
  # LP の値（conditional は分母で割る）
  res_min <- smin$optimum; res_max <- smax$optimum
  if (!is.null(obj$denom_lab)) {
    denom <- pXY_true[[obj$denom_lab]]
    if (is.na(denom) || denom<=0) { res_min <- NA_real_; res_max <- NA_real_ }
    else { res_min <- res_min/denom; res_max <- res_max/denom }
  }
  
  list(lp_lb=res_min, lp_ub=res_max, li_lb=li_lb, li_ub=li_ub,
       gap_lb = res_min - li_lb, gap_ub = li_ub - res_max)
}

# 標本化→周辺推定→LP/Li–Pearl 比較（複数 N × M）
# ===== REPLACE: sample_and_marginalize (2N_split) =====
# N は「Exp 用 N == Obs 用 N」。内部で 2N 個ドローし、前半→Exp、後半→Obs に使います。
sample_and_marginalize <- function(N, grid, po_prob, m, n){
  Z <- nrow(grid)
  idx_all <- sample.int(n = Z, size = 2L * N, replace = TRUE, prob = po_prob)
  idx_exp <- idx_all[1:N]           # 実験周辺 (pY_list) 用
  idx_obs <- idx_all[(N+1):(2*N)]   # 観測周辺 (pXY)     用
  
  # 観測周辺 P(X,Y) は Obs 部分のみ、分母は N
  tab_xy <- table(factor(grid$X[idx_obs], levels = seq_len(m)),
                  factor(grid$Y[idx_obs], levels = seq_len(n)))
  pXY_hat <- as.vector(t(tab_xy)) / N
  names(pXY_hat) <- sprintf("obs_k%d_y%d", rep(seq_len(m), each=n), rep(seq_len(n), m))
  
  # 実験周辺 P(Y_k) は Exp 部分のみ、分母は N
  pY_list_hat <- lapply(seq_len(m), function(k) {
    yk <- grid[[paste0("Y", k)]][idx_exp]
    as.numeric(table(factor(yk, levels = seq_len(n)))) / N
  })
  list(pXY = pXY_hat, pY_list = pY_list_hat)
}


run_for_obj_both_none <- function(
    obj_spec, grid, m, n, po_prob_true,
    N_joint_vals = c(10,100,1000,10000), M = 100, max_trials_factor = 20
){
  Z <- nrow(grid)
  bad_rows <- consistency_bad(grid, m)
  zero_mat <- function(idx, Z) if(length(idx)) Matrix::sparseMatrix(i=seq_along(idx), j=idx, x=1, dims=c(length(idx),Z)) else NULL
  base_blocks <- list(
    sum  = list(mat=Matrix::Matrix(1,1,Z,sparse=TRUE), dir="==", rhs=1),
    zero = list(mat=zero_mat(bad_rows,Z), dir=rep("==", length(bad_rows)), rhs=rep(0,length(bad_rows)))
  )
  mg <- build_marginals(grid, m, n)
  
  # 真値（N によらず一定）を先に計算
  obj <- make_obj(obj_spec, grid)
  true_val <- {
    num <- sum(obj$obj_vec * po_prob_true)
    if (is.null(obj$denom_lab)) num else {
      pXY_true <- as.vector(t(tapply(po_prob_true, list(grid$X, grid$Y), sum)))
      names(pXY_true) <- sprintf("obs_k%d_y%d", rep(seq_len(m), each=n), rep(seq_len(n), m))
      num / pXY_true[[obj$denom_lab]]
    }
  }
  
  rows_allN <- list()
  for (N in N_joint_vals) {
    rows <- list(); ok_cnt <- 0L; trial <- 0L
    max_trials <- max(M * max_trials_factor, M + 10L)
    
    while (ok_cnt < M && trial < max_trials) {
      trial <- trial + 1L
      # 1) 標本化→周辺推定（Li–Pearl もこの推定量で）
      marg <- sample_and_marginalize(N, grid, po_prob_true, m, n)
      pXY  <<- marg$pXY
      pY_list <<- marg$pY_list
      
      # 2) both×none の等式
      add <- list(
        mat = rbind(mg$mat_exp, mg$mat_obs),
        dir = rep("==", nrow(mg$mat_exp)+nrow(mg$mat_obs)),
        rhs = c(unlist(pY_list), as.numeric(pXY))
      )
      
      mats <- lapply(c(base_blocks, list(marg=add)), `[[`, "mat")
      keep <- !sapply(mats, is.null)
      A    <- do.call(rbind, mats[keep])
      dir  <- unlist(lapply(c(base_blocks, list(marg=add))[keep], `[[`, "dir"))
      rhs  <- unlist(lapply(c(base_blocks, list(marg=add))[keep], `[[`, "rhs"))
      
      # 3) LP solve
      smin <- run_lp_safe(obj$obj_vec, A, dir, rhs, FALSE)
      smax <- run_lp_safe(obj$obj_vec, A, dir, rhs, TRUE)
      feasible <- (!is.null(smin$status) && smin$status==0) && (!is.null(smax$status) && smax$status==0)
      
      # 4) Li–Pearl 境界
      li <- compute_lipearl_bounds_for_obj(obj_spec, m, n)
      li_lb <- if (is.null(li)) NA_real_ else as.numeric(li$lb)
      li_ub <- if (is.null(li)) NA_real_ else as.numeric(li$ub)
      check_lipearl_sanity(obj_spec, li_lb, li_ub, m, n)
      
      # 5) LP の値（conditional は分母で割る）
      res_min <- smin$optimum; res_max <- smax$optimum
      if (!is.null(obj$denom_lab)) {
        denom <- pXY[[obj$denom_lab]]
        if (is.na(denom) || denom<=0) { res_min <- NA_real_; res_max <- NA_real_ }
        else { res_min <- res_min/denom; res_max <- res_max/denom }
      }
      
      # 6) feasible のときだけ保存
      if (feasible) {
        ok_cnt <- ok_cnt + 1L
        rows[[length(rows)+1]] <- data.frame(
          N_joint=N, rep=ok_cnt, min_val=res_min, max_val=res_max,
          li_lb=li_lb, li_ub=li_ub,
          stringsAsFactors = FALSE
        )
      }
    }
    if (length(rows)) rows_allN[[length(rows_allN)+1]] <- dplyr::bind_rows(rows)
  }
  
  res_df <- if (length(rows_allN)) dplyr::bind_rows(rows_allN) else
    tibble::tibble(N_joint=integer(), rep=integer(),
                   min_val=double(), max_val=double(),
                   li_lb=double(), li_ub=double())
  
  safe_mean <- function(x) if (all(is.na(x))) NA_real_ else mean(x, na.rm=TRUE)
  safe_q    <- function(x, p) if (all(is.na(x))) NA_real_ else as.numeric(stats::quantile(x, probs=p, na.rm=TRUE, names=FALSE))
  summary_tbl <- res_df |>
    dplyr::group_by(N_joint) |>
    dplyr::summarise(
      mean_lb  = safe_mean(min_val),  ci_lb_lo = safe_q(min_val, 0.025), ci_lb_hi = safe_q(min_val, 0.975),
      mean_ub  = safe_mean(max_val),  ci_ub_lo = safe_q(max_val, 0.025), ci_ub_hi = safe_q(max_val, 0.975),
      li_mean_lb  = safe_mean(li_lb), li_ci_lb_lo = safe_q(li_lb, 0.025), li_ci_lb_hi = safe_q(li_lb, 0.975),
      li_mean_ub  = safe_mean(li_ub), li_ci_ub_lo = safe_q(li_ub, 0.025), li_ci_ub_hi = safe_q(li_ub, 0.975),
      .groups="drop"
    ) |>
    dplyr::mutate(true = true_val)
  
  list(results=res_df, summary=summary_tbl, true=true_val)
}

# =========================
# 7) Objective specs（例：Thm.4–11 + いくつか）
# =========================
obj_specs <- list()

# Table 7 題材: P(Y0=0, Y1=0, Y2=1) → (Y1=1, Y2=1, Y3=2)
obj_specs[["P(Y0=0,Y1=0,Y2=1)"]] <- list(
  type="joint", target_eq = { v <- rep(NA, m); v[1] <- 1; v[2] <- 1; v[3] <- 2; v }
)

# Thm.4: PPre(i,j) = P(Y_i^{x_j}, y_i)
obj_specs[["Thm4_PPre(i=2,j=1)"]] <- list(
  type="joint", target_eq = { v <- rep(NA,m); v[1] <- 2; v }, condY = 2
)

# Thm.5
obj_specs[["Thm5_PRep(i=1,j=3,k=2)"]] <- list(
  type="joint", target_eq = { v <- rep(NA,m); v[3] <- 1; v }, condY = 2
)

# Thm.6
obj_specs[["Thm6_PSub(i=3,j=2,kx=1)"]] <- list(
  type="joint", target_eq = { v <- rep(NA,m); v[2] <- 3; v }, condX = 1
)

# Thm.7
obj_specs[["Thm7_PN(i=2,j=1,k=3,p=2)"]] <- list(
  type="joint", target_eq = { v <- rep(NA,m); v[1] <- 2; v }, condX = 2, condY = 3
)

# Thm.8: PNS(2)
obj_specs[["Thm8_PNS2(i1=1,j1=1;i2=3,j2=3)"]] <- list(
  type="joint", target_eq = { v <- rep(NA,m); v[1] <- 1; v[3] <- 3; v }
)

# Thm.9
obj_specs[["Thm9_PSub(k=2,p=2)"]] <- list(
  type="joint", target_eq = { v <- rep(NA,m); v[1] <- 1; v[3] <- 3; v }, condX = 2
)

# Thm.10
obj_specs[["Thm10_PRep(k=2,q=2)"]] <- list(
  type="joint", target_eq = { v <- rep(NA,m); v[1] <- 1; v[3] <- 3; v }, condY = 2
)

# Thm.11
obj_specs[["Thm11_PN(k=2,p=2,q=3)"]] <- list(
  type="joint", target_eq = { v <- rep(NA,m); v[1] <- 1; v[3] <- 3; v }, condX = 2, condY = 3
)

# 追加
obj_specs[["PNS3(i1=1,j1=1;i2=2,j2=2;i3=3,j3=3)"]] <- list(
  type="joint", target_eq = { v <- rep(NA, m); v[1] <- 1; v[2] <- 2; v[3] <- 3; v }
)
obj_specs[["PRep2_mixed(q=2; i1=1,j1=1; i2=3,j2=3)"]] <- list(
  type="joint", target_eq = { v <- rep(NA, m); v[1] <- 1; v[3] <- 3; v }, condY = 2
)
obj_specs[["PN2_mixed(p=2,q=2; i1=1,j1=1; i2=3,j2=3)"]] <- list(
  type="joint", target_eq = { v <- rep(NA, m); v[1] <- 1; v[3] <- 3; v }, condX = 2, condY = 2
)

##更に追加
obj_specs[["PNS3(i1=1,j1=1;i2=1,j2=1;i3=2,j3=2)"]] <- list(
  type="joint", target_eq = { v <- rep(NA, m); v[1] <- 1; v[2] <- 1; v[3] <- 2; v }
)

# =========================
# 8) Helper: 初期値の可視化
# =========================
print_initial_state <- function(po_prob_true, grid, m, n, a_xy = NULL, top_k = 12){
  if (is.null(a_xy)) a_xy <- compute_a_xy_from_joint(po_prob_true, grid, m, n)
  cat("---- a_xy = P(X,Y) ----\n")
  print(round(a_xy, 4))
  cat("\n---- check: a_xy from joint (recomputed) ----\n")
  print(round(compute_a_xy_from_joint(po_prob_true, grid, m, n), 4))
  cat("\n---- top rows of P(Y1,..,Ym, X, Y) ----\n")
  ord <- order(po_prob_true, decreasing = TRUE)
  top <- head(ord, top_k)
  print(cbind(grid[top, ], prob = round(po_prob_true[top], 6)))
}






# =========================
# 9) EXECUTION (CLEAN)
# =========================
#set.seed(42)

# ▼▼▼ ここで “真値の作り方” を選ぶ（A/B/C_dirichlet/C_sampling） ▼▼▼
TRUTH_MODE <- "A"   # "A" | "B" | "C_dirichlet" | "C_sampling"

# A 用の観測周辺（A: この a_xy を保ったまま (X,Y) セル内だけランダム割付）
a_xy_A <- matrix(c(
  0.34, 0.00, 0.00,
  0.00, 0.32, 0.00,
  0.00, 0.00, 0.34
), nrow = m, byrow = TRUE)

# モード別パラメータ（必要に応じて調整）
alpha_cell_A <- 0.7        # A: セル内 Dirichlet 濃度
alpha_xy_B   <- 0.6        # B: a_xy Dirichlet 濃度
alpha_cell_B <- 0.6        # B: セル内 Dirichlet 濃度
alpha_C      <- 0.8        # C(dirichlet): 全体 Dirichlet 濃度
Ndraw_C      <- 20000      # C(sampling): 抽選回数
enforce_mono <- FALSE      # 単調性を課すなら TRUE

# 行の重み（任意）：(Y0=0 と Y2=2 を少し持ち上げる例）
row_w <- function(row) (row$Y1==1) + (row$Y3==3) + 1

# ---- 真値ジョイント P(Y0,Y1,Y2,X,Y) と a_xy を作る ----
if (TRUTH_MODE == "A") {
  a_xy <- a_xy_A / sum(a_xy_A)
  po_prob_true <- make_true_joint_random_from_a_xy(
    a_xy, grid, m, n, alpha = alpha_cell_A,
    enforce_monotone = enforce_mono, row_weight = row_w
  )
} else if (TRUTH_MODE == "B") {
  rnd <- make_true_joint_fully_random(
    grid, m, n, alpha_xy = alpha_xy_B, alpha_cell = alpha_cell_B,
    enforce_monotone = enforce_mono, row_weight = row_w
  )
  a_xy <- rnd$a_xy
  po_prob_true <- rnd$po_prob_true
} else if (TRUTH_MODE == "C_dirichlet") {
  po_prob_true <- make_true_joint_direct_random(
    grid, m, n, method="dirichlet", alpha = alpha_C,
    enforce_monotone = enforce_mono, row_weight = row_w
  )
  a_xy <- compute_a_xy_from_joint(po_prob_true, grid, m, n)
} else if (TRUTH_MODE == "C_sampling") {
  po_prob_true <- make_true_joint_direct_random(
    grid, m, n, method="sampling", N_joint_draws = Ndraw_C,
    enforce_monotone = enforce_mono, row_weight = row_w
  )
  a_xy <- compute_a_xy_from_joint(po_prob_true, grid, m, n)
} else {
  stop("Unknown TRUTH_MODE")
}

# ---- (X,Y) 層別の tidy テーブルを用意：P(Y0,Y1,Y2,X,Y) と P(Y0,Y1,Y2|X,Y) ----
make_joint_tidy <- function(po_prob_true, grid) {
  df <- cbind(grid[, c("Y1","Y2","Y3","X","Y")], p = po_prob_true)
  # 表示は論文の 0,1,2 に合わせる（内部は 1..3）
  dplyr::transmute(
    df,
    X = as.integer(X), Y = as.integer(Y),
    Y0 = Y1 - 1L, Y1 = Y2 - 1L, Y2 = Y3 - 1L,
    p_joint = p
  ) |>
    dplyr::arrange(X, Y, Y0, Y1, Y2)
}

make_conditional_tidy <- function(joint_df, a_xy, m, n) {
  # a_xy[x,y] で割って P(Y0,Y1,Y2 | X=x,Y=y) を作る（a_xy=0 のセルは NA）
  axydf <- tibble::tibble(
    X = rep(seq_len(m), times = n),
    Y = rep(seq_len(n), each  = m),
    a_xy = as.numeric(a_xy)
  )
  joint_df |>
    dplyr::left_join(axydf, by = c("X","Y")) |>
    dplyr::mutate(p_cond = ifelse(a_xy > 0, p_joint / a_xy, NA_real_)) |>
    dplyr::select(X, Y, Y0, Y1, Y2, p_joint, p_cond)
}

joint_df <- make_joint_tidy(po_prob_true, grid)
cond_df  <- make_conditional_tidy(joint_df, a_xy, m, n)

# ---- 本来の計算（Li-Pearl vs LP）を実行：RESULTS_Li_COMPARE に格納 ----
N_joint_vals <- c(10, 100, 1000, 10000)
M_reps <- 100

RESULTS_Li_COMPARE_0913 <- purrr::imap(obj_specs, function(spec, nm) {
  run_for_obj_both_none(
    obj_spec = spec, grid = grid, m = m, n = n, po_prob_true = po_prob_true,
    N_joint_vals = N_joint_vals, M = M_reps
  )
})

# ---- 目的関数ごとの真値を 1 テーブルに（summary 内にも true は入っています）----
true_table <- tibble::tibble(
  objective = names(RESULTS_Li_COMPARE_0913),
  true = vapply(RESULTS_Li_COMPARE_0913, function(x) x$true, numeric(1))
) |>
  dplyr::arrange(objective)

# =========================
#  出力（この3つのみ）
# =========================
cat("=== (1) a_xy = P(X,Y) ===\n")
print(round(a_xy, 6))

cat("\n=== (2) True values per objective ===\n")
print(true_table)

cat("\n=== (3) Stratified table: P(Y0,Y1,Y2|X,Y) with P(Y0,Y1,Y2,X,Y) ===\n")
print(dplyr::as_tibble(cond_df))

# （オプション）CSV 保存したい場合は以下を解放：
# readr::write_csv(true_table, "true_values.csv")
# readr::write_csv(joint_df,  "joint_PY012_XY.csv")   # P(Y0,Y1,Y2,X,Y)
# readr::write_csv(cond_df,   "cond_PY012_given_XY.csv")  # P(Y0,Y1,Y2|X,Y)
# write.csv(a_xy, "a_xy.csv", row.names = FALSE)



# 0/1/2 表示の tidy 版（あなたのコード既存）
joint_df <- make_joint_tidy(po_prob_true, grid)

utils::View(joint_df, title = "P(Y0,Y1,Y2,X,Y)")

