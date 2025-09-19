# =========================================
# 最小・素朴版（目的限定）＋ TikZ 図出力
# =========================================
# 必要パッケージ
# install.packages(c("Rglpk","Matrix","tikzDevice"))
library(Rglpk)
library(Matrix)
library(tikzDevice)

#set.seed(1)

# -------- 0) 基本パラメータ --------
m <- 3           # Y0..Y2 の個数
n <- 3           # 各Yの取りうる値 {1,2,3}
N <- 1000        # Nexp = Nobs = N
M <- 100         # 可解サンプル数
theta_seq <- c(0.00, 0.70, 0.75, 0.80, seq(0.85, 1.00, by=0.01))

# -------- 1) グリッド --------
Y_list <- setNames(lapply(seq_len(m), \(.) seq_len(n)), paste0("Y", seq_len(m)))
grid <- do.call(expand.grid, c(Y_list, list(X = seq_len(m)), list(Y = seq_len(n))))
Z <- nrow(grid)

# 単調(Y0<=Y1<=Y2)セルのインデックス
monotone_idx <- function(grid, m){
  ok <- rep(TRUE, nrow(grid))
  for(i in 1:(m-1)) ok <- ok & (grid[[paste0("Y",i)]] <= grid[[paste0("Y",i+1)]])
  which(ok)
}
MONO_IDX <- monotone_idx(grid, m)

# 一貫性違反（pick(Y_X) != 実現Y）は上限0
consistency_bad <- function(grid, m){
  Y_cols <- paste0("Y", seq_len(m))
  Y_mat  <- as.matrix(grid[, Y_cols])
  picked <- Y_mat[cbind(seq_len(nrow(grid)), as.integer(grid$X))]
  which(picked != grid$Y)
}
UB0_IDX <- consistency_bad(grid, m)

# -------- 2) “真の”PO分布（任意だが θ=1 を満たすよう構築） --------
a_xy <- matrix(c(
  0.15, 0.10, 0.10,
  0.10, 0.20, 0.10,
  0.05, 0.10, 0.10
), nrow=m, byrow=TRUE)
a_xy <- a_xy / sum(a_xy)

good_idx <- intersect(setdiff(seq_len(nrow(grid)), UB0_IDX), MONO_IDX)
den_xy <- table(factor(grid$X[good_idx], levels=1:m),
                factor(grid$Y[good_idx], levels=1:n))
den_xy <- as.matrix(den_xy); stopifnot(all(den_xy > 0))

po_prob <- numeric(Z)
po_prob[good_idx] <- a_xy[cbind(grid$X[good_idx], grid$Y[good_idx])] /
  den_xy[cbind(grid$X[good_idx], grid$Y[good_idx])]
stopifnot(abs(sum(po_prob)-1) < 1e-12)

# -------- 3) 周辺行列（実験/観測） --------
marginal_mat <- function(idx_list, Z){
  rows <- rep(seq_along(idx_list), lengths(idx_list))
  cols <- unlist(idx_list)
  sparseMatrix(i = rows, j = cols, x = 1, dims = c(length(idx_list), Z))
}

# 実験: "exp_k{1..m}_y{1..n}"（Yk==y）
idx_exp <- vector("list", m*n); cnt <- 1
for(k in 1:m) for(y in 1:n){
  idx_exp[[cnt]] <- which(grid[[paste0("Y",k)]] == y)
  cnt <- cnt + 1
}
NM_EXP <- sprintf("exp_k%d_y%d", rep(1:m, each=n), rep(1:n, m))
mat_exp <- marginal_mat(idx_exp, Z); rownames(mat_exp) <- NM_EXP

# 観測: "obs_k{1..m}_y{1..n}"（X==k & 実現Y==y）
idx_obs <- vector("list", m*n); cnt <- 1
for(k in 1:m) for(y in 1:n){
  idx_obs[[cnt]] <- which(grid$X==k & grid$Y==y)
  cnt <- cnt + 1
}
NM_OBS <- sprintf("obs_k%d_y%d", rep(1:m, each=n), rep(1:n, m))
mat_obs <- marginal_mat(idx_obs, Z); rownames(mat_obs) <- NM_OBS

# -------- 4) 目的関数（最小限） --------
make_obj <- function(obj_spec, grid){
  Z <- nrow(grid)
  cond_mask <- rep(TRUE, Z)
  if (!is.null(obj_spec$condX)) cond_mask <- cond_mask & (grid$X == obj_spec$condX)
  if (!is.null(obj_spec$condY)) cond_mask <- cond_mask & (grid$Y == obj_spec$condY)
  
  if (obj_spec$type == "joint") {
    v <- rep(TRUE, Z)
    if (!is.null(obj_spec$target_eq)) {
      for(i in which(!is.na(obj_spec$target_eq))){
        v <- v & (grid[[paste0("Y",i)]] == obj_spec$target_eq[i])
      }
    }
    if (!is.null(obj_spec$target_ineq)) {
      for(cond in obj_spec$target_ineq){
        Yi <- grid[[paste0("Y", cond$var)]]
        v <- v & switch(cond$op,
                        "=="=Yi==cond$val, "<"=Yi<cond$val, "<="=Yi<=cond$val,
                        ">" =Yi> cond$val, ">="=Yi>=cond$val, TRUE)
      }
    }
    if (!is.null(obj_spec$condX)) v <- v & (grid$X == obj_spec$condX)
    if (!is.null(obj_spec$condY)) v <- v & (grid$Y == obj_spec$condY)
    return(list(obj_vec = as.integer(v), need_denom = FALSE,
                condX = obj_spec$condX, condY = obj_spec$condY))
  }
  
  if (obj_spec$type == "linear") {
    if (!is.null(obj_spec$w_vec)) {
      stopifnot(length(obj_spec$w_vec) == Z)
      w <- as.numeric(obj_spec$w_vec)
    } else {
      coefs <- as.numeric(obj_spec$var_coefs)
      intercept <- if (is.null(obj_spec$intercept)) 0 else as.numeric(obj_spec$intercept)
      zero_based <- isTRUE(obj_spec$zero_based)
      y_mat <- do.call(cbind, lapply(1:m, function(k){
        vals <- as.numeric(grid[[paste0("Y",k)]])
        if (zero_based) vals <- vals - 1
        vals
      }))
      w <- intercept + as.numeric(y_mat %*% coefs)
    }
    w[!cond_mask] <- 0
    need_denom <- (!is.null(obj_spec$condX) || !is.null(obj_spec$condY))
    return(list(obj_vec = w, need_denom = need_denom,
                condX = obj_spec$condX, condY = obj_spec$condY))
  }
  
  stop("unknown obj type")
}

# 例の目的関数（必要に応じて編集）
obj_specs <- list(
  "P(Y0=0,Y1=0,Y2=1)" = list(
    type="joint", target_eq=c(1,1,2), condX=NULL, condY=NULL
  ),
  "E[Y1-Y0 | X=2,Y=2]" = list(
    type="linear", var_coefs=c(-1,1,0), intercept=0, zero_based=TRUE,
    condX=3, condY=3
  )
)

needs_obs_cases <- function(spec) {
  # 実現Yに条件を入れているなら観測周辺が必須
  !is.null(spec$condY)
}

# 条件付き線形の分母（観測由来）
get_denom_from_obs <- function(condX, condY, b_obs){
  if (is.null(condX) && is.null(condY)) return(1)
  if (!is.null(condX) && !is.null(condY)) {
    nm <- sprintf("obs_k%d_y%d", condX, condY); return(b_obs[nm])
  }
  if (!is.null(condX)) {
    nms <- sprintf("obs_k%d_y%d", condX, 1:n); return(sum(b_obs[nms]))
  }
  if (!is.null(condY)) {
    nms <- sprintf("obs_k%d_y%d", 1:m, condY); return(sum(b_obs[nms]))
  }
  1
}

# -------- 5) 単純LPラッパ --------
run_lp <- function(obj, A, dir, rhs, maximise=FALSE){
  nvar <- length(obj)
  ub <- rep(1, nvar)
  if (length(UB0_IDX)) ub[UB0_IDX] <- 0
  bounds <- list(
    lower = list(ind = 1:nvar, val = rep(0, nvar)),
    upper = list(ind = 1:nvar, val = ub)
  )
  Rglpk_solve_LP(obj=obj, mat=A, dir=dir, rhs=rhs, bounds=bounds, max=maximise,
                 control=list(canonicalize_status=TRUE, presolve=TRUE, verbose=FALSE))
}

# 制約（合計=1、単調イベント >= theta、case別の周辺）
build_constraints <- function(case_name, b_exp=NULL, b_obs=NULL, theta=0){
  A <- Matrix(1, 1, Z, sparse=TRUE); dir <- "=="; rhs <- 1
  if (theta > 0) {
    row_mono <- sparseMatrix(i=rep(1,length(MONO_IDX)), j=MONO_IDX, x=1, dims=c(1,Z))
    A <- rbind(A, row_mono); dir <- c(dir, ">="); rhs <- c(rhs, theta)
  }
  if (case_name %in% c("exp","both")) {
    A <- rbind(A, mat_exp); dir <- c(dir, rep("==", nrow(mat_exp))); rhs <- c(rhs, as.numeric(b_exp[NM_EXP]))
  }
  if (case_name %in% c("obs","both")) {
    A <- rbind(A, mat_obs); dir <- c(dir, rep("==", nrow(mat_obs))); rhs <- c(rhs, as.numeric(b_obs[NM_OBS]))
  }
  list(A=A, dir=dir, rhs=rhs)
}

# θ=1 & case="both" で可解か（サンプル採択条件）
feasible_both_theta1 <- function(b_exp, b_obs){
  cs <- build_constraints("both", b_exp, b_obs, theta=1)
  sol <- run_lp(obj = rep(0, Z), A=cs$A, dir=cs$dir, rhs=cs$rhs, maximise=FALSE)
  !is.null(sol$status) && sol$status==0
}

# -------- 6) サンプルを一度だけ M 個作る（split 2N） --------
draw_M_pairs <- function(N, M){
  out <- vector("list", M)
  r <- 0; tries <- 0; MAX_TRIES <- 1e7
  while(r < M){
    tries <- tries + 1
    idx <- sample.int(Z, size=2*N, replace=TRUE, prob=po_prob)
    idx_exp <- idx[1:N]; idx_obs <- idx[(N+1):(2*N)]
    # 実験周辺
    b_exp <- numeric(m*n); names(b_exp) <- NM_EXP
    for(k in 1:m){
      yk <- grid[[paste0("Y",k)]][idx_exp]
      tab <- tabulate(yk, nbins=n)/N
      for(y in 1:n) b_exp[sprintf("exp_k%d_y%d", k, y)] <- tab[y]
    }
    # 観測周辺
    b_obs <- numeric(m*n); names(b_obs) <- NM_OBS
    xybin <- (grid$X[idx_obs]-1)*n + grid$Y[idx_obs]
    tab <- tabulate(xybin, nbins=m*n)/N
    b_obs[] <- tab
    
    if (feasible_both_theta1(b_exp, b_obs)) {
      r <- r + 1
      out[[r]] <- list(b_exp=b_exp, b_obs=b_obs)
    }
    if (tries > MAX_TRIES) stop("採択サンプルが見つかりませんでした（上限到達）")
  }
  out
}

cat("サンプル生成中...\n")
PINNED <- draw_M_pairs(N, M)
cat("サンプル完了: ", length(PINNED), "個\n")

# -------- 7) 評価（全目的関数×θ、exp/obs/both） --------
evaluate_all <- function(obj_specs, pinned_samples, theta_seq){
  summary_rows <- list()
  rep_rows <- list()
  row_id <- 0L
  
  for (obj_name in names(obj_specs)) {
    spec <- obj_specs[[obj_name]]
    obj_info <- make_obj(spec, grid)
    
    # 実現Yに条件が入る目的は exp を評価対象から外す
    case_candidates <- if (needs_obs_cases(spec)) c("obs","both") else c("exp","obs","both")
    
    for (th in theta_seq) {
      for (case_name in case_candidates) {
        mins <- numeric(length(pinned_samples))
        maxs <- numeric(length(pinned_samples))
        feas <- logical(length(pinned_samples))
        deno <- numeric(length(pinned_samples)); deno[] <- 1
        
        for (r in seq_along(pinned_samples)) {
          b_exp <- pinned_samples[[r]]$b_exp
          b_obs <- pinned_samples[[r]]$b_obs
          
          # 制約生成（case と theta に依存）
          cs <- build_constraints(case_name, b_exp, b_obs, theta = th)
          
          # 目的（分子）の LP（min/max）
          sol_min <- run_lp(obj_info$obj_vec, cs$A, cs$dir, cs$rhs, maximise = FALSE)
          sol_max <- run_lp(obj_info$obj_vec, cs$A, cs$dir, cs$rhs, maximise = TRUE)
          
          ok <- (!is.null(sol_min$status) && sol_min$status == 0) &&
            (!is.null(sol_max$status) && sol_max$status == 0)
          
          # 条件付き線形は分母を観測から取り、0 なら不可
          if (ok && obj_info$need_denom) {
            d <- get_denom_from_obs(obj_info$condX, obj_info$condY, b_obs)
            if (is.na(d) || d <= 0) {
              ok <- FALSE
            } else {
              deno[r] <- d
            }
          }
          
          feas[r] <- ok
          mins[r] <- if (ok) sol_min$optimum / deno[r] else NA_real_
          maxs[r] <- if (ok) sol_max$optimum / deno[r] else NA_real_
        }
        
        # 集計（NA 安全版）
        safe_mean <- function(x) if (all(is.na(x))) NA_real_ else mean(x, na.rm = TRUE)
        safe_q    <- function(x, p) if (all(is.na(x))) NA_real_ else as.numeric(quantile(x, probs = p, na.rm = TRUE, names = FALSE))
        
        row_id <- row_id + 1L
        summary_rows[[row_id]] <- data.frame(
          obj = obj_name, theta = th, case = case_name,
          n_rep = length(pinned_samples),
          n_feasible = sum(feas, na.rm = TRUE),
          mean_lb = safe_mean(mins),  ci_lb_lo = safe_q(mins, 0.025), ci_lb_hi = safe_q(mins, 0.975),
          mean_ub = safe_mean(maxs),  ci_ub_lo = safe_q(maxs, 0.025), ci_ub_hi = safe_q(maxs, 0.975),
          stringsAsFactors = FALSE
        )
        
        rep_rows[[row_id]] <- data.frame(
          obj = obj_name, theta = th, case = case_name,
          rep = seq_along(pinned_samples),
          feasible = feas, lb = mins, ub = maxs, denom = deno,
          stringsAsFactors = FALSE
        )
      }
    }
  }
  
  summary_df <- do.call(rbind, summary_rows)
  reps_df    <- do.call(rbind, rep_rows)
  list(summary = summary_df, replicates = reps_df)
}

cat("最適化・集計中...\n")
RES_ALL <- evaluate_all(obj_specs, PINNED, theta_seq)
cat("完了\n")

# -------- 8) 保存用のアーカイブを作成 --------
SIMPLE_RUN_ARCHIVE <- list(
  meta = list(
    m = m, n = n, N = N, M = M,
    theta_seq = theta_seq,
    seed = 1L,
    timestamp = as.character(Sys.time())
  ),
  grid = grid,
  pinned_samples = PINNED,              # M個の (b_exp, b_obs)
  results = list(
    summary    = RES_ALL$summary,       # 目的×θ×case の平均/CI
    replicates = RES_ALL$replicates     # 各repの下限/上限・分母・可解フラグ
  )
)




# ===== 互換アダプタ：SIMPLE_RUN_ARCHIVE → RESULT_theta_summary =====
stopifnot(exists("SIMPLE_RUN_ARCHIVE"))

# 真値 true の付与
true_from_po <- function(obj_spec, grid, po_prob){
  mk <- make_obj(obj_spec, grid)
  numer <- sum(mk$obj_vec * po_prob)
  if (!isTRUE(mk$need_denom)) return(numer)
  mask <- rep(TRUE, nrow(grid))
  if (!is.null(mk$condX)) mask <- mask & (grid$X == mk$condX)
  if (!is.null(mk$condY)) mask <- mask & (grid$Y == mk$condY)
  denom <- sum(po_prob[mask])
  if (denom <= 0) return(NA_real_)
  numer / denom
}
TRUE_BY_OBJ <- setNames(
  vapply(names(obj_specs), function(nm) true_from_po(obj_specs[[nm]], grid, po_prob), numeric(1)),
  names(obj_specs)
)

RES_SUM <- SIMPLE_RUN_ARCHIVE$results$summary
RES_SUM$Nexp <- SIMPLE_RUN_ARCHIVE$meta$N
RES_SUM$Nobs <- SIMPLE_RUN_ARCHIVE$meta$N
RES_SUM$M    <- SIMPLE_RUN_ARCHIVE$meta$M
RES_SUM$scenario <- sprintf("theta<=P(Y0<=Y1<=Y2), theta=%.3f", RES_SUM$theta)
RES_SUM$true <- TRUE_BY_OBJ[RES_SUM$obj]

# 列順を元コードに寄せる
wanted_order <- c(
  "obj","theta","scenario","case","Nexp","Nobs","M",
  "n_rep","n_feasible",
  "mean_lb","ci_lb_lo","ci_lb_hi",
  "mean_ub","ci_ub_lo","ci_ub_hi","true"
)
keep <- intersect(wanted_order, names(RES_SUM))
RESULT_theta_summary <- RES_SUM[, keep, drop = FALSE]


# ============ 0913 格納アダプタ（SIMPLE_RUN_ARCHIVE/RES_ALL → 0831方式の0913名） ============
# 受け皿
`0913revised_RESULT_simulation_THETA` <- list()

# theta毎・case毎に replicates をまとめる
.split_replicates_0913 <- function(rep_df) {
  stopifnot(all(c("theta","case","rep","lb","ub") %in% names(rep_df)))
  case_levels <- c("exp","obs","both")
  by_th <- split(rep_df, rep_df$theta)
  lapply(by_th, function(df_th) {
    by_case <- split(df_th, df_th$case)
    out_case <- lapply(case_levels, function(cs) {
      x <- by_case[[cs]]
      if (is.null(x) || nrow(x) == 0) return(data.frame())
      x[, c("rep","lb","ub"), drop = FALSE]
    })
    names(out_case) <- case_levels
    out_case
  })
}

# キー（N と M は今回固定）
N_key <- sprintf("N=%d", SIMPLE_RUN_ARCHIVE$meta$N)
M_key <- sprintf("M=%d", SIMPLE_RUN_ARCHIVE$meta$M)

# theta を replicates に付与（evaluate_all()の出力を整形）
.reps_with_theta_0913 <- local({
  # summary から (theta, case, scenario) 対応を取り出して join
  map_tbl <- unique(RESULT_theta_summary[, c("theta","case","scenario")])
  reps <- merge(RES_ALL$replicates, map_tbl, by = "case", all.x = TRUE)
  # evaluat_all() 側で case×theta ごとに解いているので scenario での joinも保持
  reps
})

for (ob in unique(RESULT_theta_summary$obj)) {
  sum_ob <- subset(RESULT_theta_summary, obj == ob & case %in% c("exp","obs","both"))
  sum_ob$N <- SIMPLE_RUN_ARCHIVE$meta$N
  sum_ob$M <- SIMPLE_RUN_ARCHIVE$meta$M
  sum_ob <- sum_ob[, c("scenario","case","mean_lb","ci_lb_lo","ci_lb_hi",
                       "mean_ub","ci_ub_lo","ci_ub_hi","true","theta","N","M")]
  
  reps_ob <- subset(.reps_with_theta_0913, obj == ob)
  reps_nested <- .split_replicates_0913(reps_ob)
  
  if (is.null(`0913revised_RESULT_simulation_THETA`[[ob]]))
    `0913revised_RESULT_simulation_THETA`[[ob]] <- list()
  if (is.null(`0913revised_RESULT_simulation_THETA`[[ob]][[N_key]]))
    `0913revised_RESULT_simulation_THETA`[[ob]][[N_key]] <- list()
  if (is.null(`0913revised_RESULT_simulation_THETA`[[ob]][[N_key]][[M_key]]))
    `0913revised_RESULT_simulation_THETA`[[ob]][[N_key]][[M_key]] <-
    list(replicates_by_theta = list(), summary = data.frame())
  
  # theta ごとのレプリケート
  for (th_key in names(reps_nested)) {
    key <- sprintf("theta=%.3f", as.numeric(th_key))
    `0913revised_RESULT_simulation_THETA`[[ob]][[N_key]][[M_key]]$replicates_by_theta[[key]] <-
      reps_nested[[th_key]]
  }
  
  # サマリーを統合（重複を排除）
  old <- `0913revised_RESULT_simulation_THETA`[[ob]][[N_key]][[M_key]]$summary
  new <- sum_ob
  `0913revised_RESULT_simulation_THETA`[[ob]][[N_key]][[M_key]]$summary <-
    dplyr::bind_rows(old, new) |>
    dplyr::distinct(theta, scenario, case, .keep_all = TRUE) |>
    dplyr::arrange(theta, scenario, case)
}
# ==========================================================================================



# フラグを未定義なら与える（出力ブロックが上書きしない版も下で示します）
if (!exists("DO_TEX_OUTPUT")) DO_TEX_OUTPUT <- TRUE
if (!exists("DO_PLOTS"))      DO_PLOTS      <- TRUE
if (!exists("DO_TIKZ"))       DO_TIKZ       <- TRUE
if (!exists("TIKZ_STANDALONE")) TIKZ_STANDALONE <- FALSE


library(magrittr)
library(dplyr)



# ---- どこか上の共通部に追加（例：図ブロックの直前） ----
ggsave_pdf_safe <- function(filename, plot, width, height) {
  dir.create(dirname(filename), recursive = TRUE, showWarnings = FALSE)
  
  # まず cairo_pdf を試す（透明背景が不安定な環境があるので bg=white を固定）
  tried <- FALSE
  if (isTRUE(capabilities("cairo"))) {
    tried <- TRUE
    ok <- tryCatch({
      ggplot2::ggsave(
        filename = filename, plot = plot,
        device = cairo_pdf, width = width, height = height, units = "in",
        bg = "white"
      )
      TRUE
    }, error = function(e) FALSE)
    if (ok) return(invisible(filename))
  }
  
  # フォールバック：通常の pdf() デバイス
  tryCatch({
    ggplot2::ggsave(
      filename = filename, plot = plot,
      device = "pdf", width = width, height = height, units = "in",
      bg = "white"
    )
    invisible(filename)
  }, error = function(e) {
    stop(sprintf(
      "PDF書き出しに失敗しました。tried_cairo=%s\npath=%s\nerror=%s",
      tried, filename, conditionMessage(e)
    ), call. = FALSE)
  })
}




# === 図出力に関わる部分 全差し替えブロック =====================================

# オプショントグル例（既に定義済みなら不要）
# 置き換え推奨（安全です）
if (!exists("DO_TEX_OUTPUT")) DO_TEX_OUTPUT <- TRUE
if (!exists("DO_PLOTS"))      DO_PLOTS      <- TRUE
if (!exists("DO_TIKZ"))       DO_TIKZ       <- FALSE
if (!exists("TIKZ_STANDALONE")) TIKZ_STANDALONE <- FALSE


if (DO_TIKZ) suppressPackageStartupMessages(library(tikzDevice))

if (DO_TEX_OUTPUT || DO_PLOTS) {
  suppressPackageStartupMessages({library(ggplot2); library(scales)})
}

# -------------------- LaTeX表の出力（旧版踏襲） --------------------
if (DO_TEX_OUTPUT) {
  dir.create(file.path("tex","L_change"), recursive = TRUE, showWarnings = FALSE)
  
  fmt_ci <- function(mu, lo, hi, digits = 3) {
    out <- sprintf(paste0("%.", digits, "f [%.", digits, "f, %.", digits, "f]"), mu, lo, hi)
    bad <- is.na(mu) | is.na(lo) | is.na(hi); out[bad] <- "--"; out
  }
  fmt_num <- function(x, digits = 3) ifelse(is.finite(x), formatC(x, format = "f", digits = digits), "--")
  
  make_L_change_table_for_obj <- function(df, obj_name,
                                          Nexp_pick = 1000, Nobs_pick = 1000, M_pick = 100,
                                          digits_ci = 3, digits_L = 2) {
    df1 <- df %>%
      dplyr::filter(Nexp == Nexp_pick, Nobs == Nobs_pick, M == M_pick, case %in% c("exp","obs","both")) %>%
      dplyr::select(theta, case, mean_lb, ci_lb_lo, ci_lb_hi, mean_ub, ci_ub_lo, ci_ub_hi)
    if (nrow(df1) == 0L) return(character(0))
    obs_row <- df1 %>% dplyr::filter(case == "obs") %>% dplyr::slice(1)
    obs_lb  <- if (nrow(obs_row) > 0) fmt_ci(obs_row$mean_lb, obs_row$ci_lb_lo, obs_row$ci_lb_hi, digits_ci) else "--"
    obs_ub  <- if (nrow(obs_row) > 0) fmt_ci(obs_row$mean_ub, obs_row$ci_ub_lo, obs_row$ci_ub_hi, digits_ci) else "--"
    df_exp  <- df1 %>% dplyr::filter(case == "exp")
    df_both <- df1 %>% dplyr::filter(case == "both")
    thetas  <- sort(unique(c(df_exp$theta, df_both$theta)))
    
    header <- c(
      "\\begin{table}[!htbp]","\\centering",
      sprintf("\\caption{Bounds vs $L$ for %s (N$_\\mathrm{exp}$ = %d, N$_\\mathrm{obs}$ = %d, M = %d)}",
              obj_name, Nexp_pick, Nobs_pick, M_pick),
      "\\begin{tabular}{cc|cc}","\\hline\\hline",
      "Scenario & $L$ & LB & UB \\\\","\\hline\\hline"
    )
    body <- character(0)
    body <- c(body, sprintf("Obs & -- & %s & %s \\\\", obs_lb, obs_ub), "\\hline")
    for (L in thetas) {
      ex <- df_exp  %>% dplyr::filter(theta == L) %>% dplyr::slice(1)
      bt <- df_both %>% dplyr::filter(theta == L) %>% dplyr::slice(1)
      has_exp  <- nrow(ex) == 1 && is.finite(ex$mean_lb) && is.finite(ex$mean_ub)
      has_both <- nrow(bt) == 1 && is.finite(bt$mean_lb) && is.finite(bt$mean_ub)
      pick <- if (has_exp) ex else bt
      scen <- if (has_exp && has_both) "Exp. \\& Both" else if (has_exp) "Exp." else if (has_both) "Both" else "--"
      eb_lb <- if (!is.null(pick) && nrow(pick) == 1) fmt_ci(pick$mean_lb, pick$ci_lb_lo, pick$ci_lb_hi, digits_ci) else "--"
      eb_ub <- if (!is.null(pick) && nrow(pick) == 1) fmt_ci(pick$mean_ub, pick$ci_ub_lo, pick$ci_ub_hi, digits_ci) else "--"
      Ltxt <- formatC(L, format = "f", digits = digits_L)
      body <- c(body, sprintf("%s & %s & %s & %s \\\\", scen, Ltxt, eb_lb, eb_ub))
    }
    footer <- c("\\hline","\\end{tabular}","\\end{table}")
    c(header, body, footer)
  }
  
  stopifnot(exists("RESULT_theta_summary"), is.data.frame(RESULT_theta_summary))
  objs <- unique(RESULT_theta_summary$obj)
  for (ob in objs) {
    df_ob <- dplyr::filter(RESULT_theta_summary, obj == ob)
    lines <- make_L_change_table_for_obj(df_ob, ob,
                                         Nexp_pick = 1000, Nobs_pick = 1000, M_pick = 100,
                                         digits_ci = 3, digits_L = 2)
    if (length(lines) == 0L) {
      message(sprintf("[warn] %s: Nexp=1000, Nobs=1000, M=100 の結果が無いのでスキップ。", ob)); next
    }
    out_name <- paste0(gsub("[^A-Za-z0-9]+","_", ob), "_Nexp1000_Nobs1000_M100.tex")
    fname <- file.path("tex","L_change", out_name)
    writeLines(lines, con = fname, useBytes = TRUE)
    message("wrote: ", fname)
  }
}

# -------------------- 図の出力（旧版踏襲：凡例付き合成図を保存） --------------------
if (DO_PLOTS) {
  suppressPackageStartupMessages({library(ggplot2); library(dplyr); library(scales); library(cowplot)})
  
  out_dir_fig_bx <- file.path("tex", "L_change", "fig_brokenx")
  dir.create(out_dir_fig_bx, recursive = TRUE, showWarnings = FALSE)
  
  piecewise_x_trans <- function(split_at = 0.85, width_left = 1, width_right = 3) {
    stopifnot(split_at > 0, split_at < 1, width_left > 0, width_right > 0)
    r <- width_left / (width_left + width_right)
    fwd <- function(x) ifelse(x <= split_at, (r / split_at) * x, r + ((x - split_at) / (1 - split_at)) * (1 - r))
    inv <- function(u) ifelse(u <= r, (split_at / r) * u, split_at + ((u - r) / (1 - r)) * (1 - split_at))
    scales::trans_new(name = sprintf("piecewise_x_%.2f_%.2f_%.2f", split_at, width_left, width_right), transform = fwd, inverse = inv)
  }
  
  make_theta_lineplots_for_obj_brokenx_trans <- function(
    df_all, obj_name,
    Nexp_pick = 1000, Nobs_pick = 1000, M_pick = 100,
    split_at = 0.85, width_left = 1, width_right = 3,
    right_major_by = 0.02, show_obs = TRUE,
    emit_tikz = FALSE, tikz_standalone = FALSE
  ){
    df1 <- df_all %>%
      dplyr::filter(Nexp == Nexp_pick, Nobs == Nobs_pick, M == M_pick, case %in% c("exp","both","obs")) %>%
      dplyr::select(theta, case, mean_lb, ci_lb_lo, ci_lb_hi, mean_ub, ci_ub_lo, ci_ub_hi, true)
    if (nrow(df1) == 0L) return(invisible(NULL))
    true_vals <- df1 %>% dplyr::filter(is.finite(true)) %>% dplyr::distinct(true) %>% dplyr::pull(true)
    true_val  <- if (length(true_vals)) true_vals[1] else NA_real_
    df_exp  <- df1 %>% dplyr::filter(case == "exp",  is.finite(mean_lb), is.finite(mean_ub))
    df_both <- df1 %>% dplyr::filter(case == "both", is.finite(mean_lb), is.finite(mean_ub))
    thetas <- sort(unique(c(df_exp$theta, df_both$theta)))
    if (!length(thetas)) return(invisible(NULL))
    
    picked_rows <- lapply(thetas, function(L) {
      ex <- df_exp  %>% dplyr::filter(theta == L) %>% dplyr::slice(1)
      if (nrow(ex) == 1) return(cbind(ex, src = "Exp."))
      bt <- df_both %>% dplyr::filter(theta == L) %>% dplyr::slice(1)
      if (nrow(bt) == 1) return(cbind(bt, src = "Both"))
      NULL
    })
    picked_rows <- Filter(Negate(is.null), picked_rows)
    if (!length(picked_rows)) return(invisible(NULL))
    df_pick <- dplyr::bind_rows(picked_rows)
    
    used_src  <- unique(df_pick$src)
    base_lab  <- if ("Exp." %in% used_src) "Exp./Both" else "Both"
    lblb <- paste0("LB (", base_lab, ")")
    ubeb <- paste0("UB (", base_lab, ")")
    
    ci_item_lb      <- paste0("LB (", base_lab, ")")
    ci_item_ub      <- paste0("UB (", base_lab, ")")
    ci_item_lb_obs  <- "LB (Obs.)"
    ci_item_ub_obs  <- "UB (Obs.)"
    ci_title_pdf  <- "95% CI"
    ci_title_tikz <- "95\\% CI"
    ci_title_str  <- if (isTRUE(emit_tikz)) ci_title_tikz else ci_title_pdf
    
    plot_df <- df_pick %>% dplyr::transmute(theta = as.numeric(theta),
                                            mean_lb, ci_lb_lo, ci_lb_hi,
                                            mean_ub, ci_ub_lo, ci_ub_hi) %>%
      dplyr::arrange(theta)
    
    plot_long <- dplyr::bind_rows(
      plot_df %>% dplyr::transmute(theta, value = mean_lb, series = lblb),
      plot_df %>% dplyr::transmute(theta, value = mean_ub, series = ubeb)
    ) %>% dplyr::filter(is.finite(theta), is.finite(value))
    
    points_long <- plot_long
    
    # 折れ線は点が2つ以上ある系列だけを対象にする（1点だけの系列は線を引かない）
    plot_line <- points_long %>%
      dplyr::group_by(series) %>%
      dplyr::filter(dplyr::n() >= 2) %>%
      dplyr::ungroup()
    
    
    obs_row <- df1 %>% dplyr::filter(case == "obs") %>% dplyr::slice(1)
    has_obs <- isTRUE(show_obs) && nrow(obs_row) == 1 &&
      is.finite(obs_row$mean_lb) && is.finite(obs_row$mean_ub) &&
      is.finite(obs_row$ci_lb_lo) && is.finite(obs_row$ci_lb_hi) &&
      is.finite(obs_row$ci_ub_lo) && is.finite(obs_row$ci_ub_hi)
    
    rib_long <- dplyr::bind_rows(
      df_pick %>% dplyr::transmute(theta = as.numeric(theta),
                                   ymin = ci_lb_lo, ymax = ci_lb_hi,
                                   ci_series = ci_item_lb),
      df_pick %>% dplyr::transmute(theta = as.numeric(theta),
                                   ymin = ci_ub_lo, ymax = ci_ub_hi,
                                   ci_series = ci_item_ub)
    ) %>% dplyr::filter(is.finite(ymin), is.finite(ymax))
    
    obs_ribbon <- data.frame()
    if (has_obs && length(plot_df$theta) > 0 &&
        is.finite(suppressWarnings(min(plot_df$theta))) &&
        is.finite(suppressWarnings(max(plot_df$theta)))) {
      x_min <- suppressWarnings(min(plot_df$theta, na.rm = TRUE))
      x_max <- suppressWarnings(max(plot_df$theta, na.rm = TRUE))
      obs_ribbon <- rbind(
        data.frame(xmin = x_min, xmax = x_max, ymin = obs_row$ci_lb_lo, ymax = obs_row$ci_lb_hi, ci_series = ci_item_lb_obs),
        data.frame(xmin = x_min, xmax = x_max, ymin = obs_row$ci_ub_lo, ymax = obs_row$ci_ub_hi, ci_series = ci_item_ub_obs)
      )
      obs_ribbon <- obs_ribbon[is.finite(obs_ribbon$ymin) & is.finite(obs_ribbon$ymax), , drop = FALSE]
    }
    
    fill_vals <- c(
      setNames("#9a9a9a", ci_item_lb),
      setNames("#8c8c8c", ci_item_ub),
      setNames("#b5b5b5", ci_item_lb_obs),
      setNames("#a8a8a8", ci_item_ub_obs)
    )
    
    true_long <- if (is.finite(true_val)) {
      tibble::tibble(theta = range(plot_df$theta, na.rm = TRUE),
                     value = true_val, series = "True")
    } else tibble::tibble(theta = numeric(0), value = numeric(0), series = character(0))
    
    obs_lines <- if (has_obs) {
      data.frame(series = c("LB (Obs.)","UB (Obs.)"),
                 y = c(obs_row$mean_lb, obs_row$mean_ub),
                 stringsAsFactors = FALSE)
    } else data.frame(series = character(0), y = numeric(0))
    
    tr <- piecewise_x_trans(split_at = split_at, width_left = width_left, width_right = width_right)
    breaks_left  <- c(0, 0.50, split_at)
    breaks_right <- seq(split_at, 1.0, by = right_major_by)
    axis_breaks  <- sort(unique(c(breaks_left, breaks_right)))
    axis_labels  <- formatC(axis_breaks, format = "f", digits = 2)
    
    y_ci_vals <- c(rib_long$ymin, rib_long$ymax, obs_ribbon$ymin, obs_ribbon$ymax)
    y_all <- c(plot_long$value, true_long$value, obs_lines$y, y_ci_vals)
    y_all <- y_all[is.finite(y_all)]
    if (length(y_all)) {
      y_min <- min(y_all); y_max <- max(y_all); dy <- y_max - y_min
      if (!is.finite(dy) || dy <= 0) dy <- 1e-6
      # 端点はみ出し対策の極小マージン
      eps <- max(1e-9, 1e-6 * dy)
      y_lower <- y_min - 0.04 * dy - eps
      y_upper <- y_max + max(0.10 * dy, 0.04) + eps
      y_lim   <- c(y_lower, y_upper)
    } else y_lim <- c(0, 1)
    
    points_plot <- points_long %>%
      dplyr::filter(value >= y_lim[1], value <= y_lim[2])
    
    lt_breaks <- c(lblb, ubeb, "LB (Obs.)", "UB (Obs.)", "True")
    lt_vals   <- c(setNames("dashed", lblb), setNames("solid",  ubeb), "longdash", "twodash", "dotted")
    names(lt_vals) <- lt_breaks
    
    # ---- 本体プロット ----
    plt_main <- ggplot2::ggplot()
    if (has_obs) {
      plt_main <- plt_main + ggplot2::geom_hline(
        data = obs_lines, ggplot2::aes(yintercept = y, linetype = series),
        linewidth = 0.30, show.legend = FALSE
      )
    }
    if (nrow(rib_long) > 0) {
      plt_main <- plt_main + ggplot2::geom_ribbon(
        data = rib_long,
        ggplot2::aes(x = theta, ymin = ymin, ymax = ymax, fill = ci_series),
        alpha = 0.22, show.legend = FALSE, inherit.aes = FALSE, na.rm = TRUE
      )
    }
    if (nrow(obs_ribbon) > 0) {
      plt_main <- plt_main + ggplot2::geom_rect(
        data = obs_ribbon,
        ggplot2::aes(xmin = xmin, xmax = xmax, ymin = ymin, ymax = ymax, fill = ci_series),
        alpha = 0.18, show.legend = FALSE, inherit.aes = FALSE, na.rm = TRUE
      )
    }
    plt_main <- plt_main +
      ggplot2::geom_line(data = plot_line, ggplot2::aes(x = theta, y = value, linetype = series),
                         linewidth = 0.65, show.legend = FALSE) +
      ggplot2::geom_point(data = points_plot, ggplot2::aes(x = theta, y = value, shape = series),
                          size = 1.9, stroke = 0.35, show.legend = FALSE, na.rm = TRUE) +
      ggplot2::geom_line(data = true_long, ggplot2::aes(x = theta, y = value, linetype = series),
                         linewidth = 0.65, show.legend = FALSE) +
      ggplot2::scale_linetype_manual(values = lt_vals, breaks = lt_breaks, name = "Bounds") +
      ggplot2::scale_fill_manual(values = fill_vals, name = ci_title_str, guide  = "none") +
      ggplot2::scale_shape_manual(values = setNames(c(1, 16), c(lblb, ubeb)), guide = "none") +
      ggplot2::scale_x_continuous(trans = tr, breaks = axis_breaks, labels = axis_labels,
                                  expand = ggplot2::expansion(mult = 0.001)) +
      ggplot2::coord_cartesian(ylim = y_lim, expand = FALSE) +
      ggplot2::labs(title = NULL, x = "L", y = NULL) +
      ggplot2::theme_bw(base_size = 12) +
      ggplot2::theme(legend.position = "none", plot.title = ggplot2::element_blank(),
                     panel.grid.major   = ggplot2::element_line(colour = "grey85", linewidth = 0.30),
                     panel.grid.minor   = ggplot2::element_blank())
    
    # ---- 凡例（線種） ----
    df_leg_bounds <- data.frame(x = 0, xend = 1, y = 1, yend = 1,
                                series = factor(lt_breaks, levels = lt_breaks))
    legend_bounds_plot <- ggplot2::ggplot(df_leg_bounds) +
      ggplot2::geom_segment(ggplot2::aes(x = x, xend = xend, y = y, yend = yend, linetype = series),
                            linewidth = 0.9, show.legend = TRUE) +
      ggplot2::scale_linetype_manual(values = lt_vals, breaks = lt_breaks, name = "Bounds") +
      ggplot2::guides(linetype = ggplot2::guide_legend(nrow = 1, byrow = TRUE)) +
      ggplot2::theme_void(base_size = 12) +
      ggplot2::theme(legend.position = "top", legend.direction = "horizontal",
                     legend.title = ggplot2::element_text(size = 8.5),
                     legend.text  = ggplot2::element_text(size = 8.5),
                     legend.key   = ggplot2::element_blank(),
                     legend.background     = ggplot2::element_blank(),
                     legend.box.background = ggplot2::element_blank())
    legend_bounds <- cowplot::get_legend(legend_bounds_plot)
    
    # ---- 凡例（CI） ----
    ci_levels <- names(fill_vals)
    df_leg_ci <- data.frame(ci_series = factor(ci_levels, levels = ci_levels), x = 1, y = 1)
    legend_ci_plot <- ggplot2::ggplot(df_leg_ci) +
      ggplot2::geom_point(ggplot2::aes(x = x, y = y, fill = ci_series), shape = 22, size = 3.2, colour = NA, show.legend = TRUE) +
      ggplot2::scale_fill_manual(values = fill_vals, breaks = names(fill_vals), name = ci_title_str) +
      ggplot2::guides(fill = ggplot2::guide_legend(nrow = 1, byrow = TRUE)) +
      ggplot2::theme_void(base_size = 12) +
      ggplot2::theme(legend.position = "top", legend.direction = "horizontal",
                     legend.title = ggplot2::element_text(size = 8.5),
                     legend.text  = ggplot2::element_text(size = 8.5),
                     legend.key   = ggplot2::element_blank(),
                     legend.background     = ggplot2::element_blank(),
                     legend.box.background = ggplot2::element_blank())
    legend_ci <- cowplot::get_legend(legend_ci_plot)
    
    legend_top <- cowplot::plot_grid(legend_bounds, legend_ci, ncol = 1, rel_heights = c(1, 1))
    plt_out <- cowplot::plot_grid(legend_top, plt_main, ncol = 1, rel_heights = c(0.18, 1))
    
    # ---- 保存（PDFはcairo優先、TikZはオプション） ----
    out_dir_pdf <- file.path("tex", "L_change", "fig_brokenx")
    dir.create(out_dir_pdf, recursive = TRUE, showWarnings = FALSE)
    out_pdf_name <- paste0(gsub("[^A-Za-z0-9]+","_", obj_name),
                           "_Nexp", Nexp_pick, "_Nobs", Nobs_pick, "_M", M_pick, "_brokenx_new2.pdf")
    out_pdf_path <- file.path(out_dir_pdf, out_pdf_name)
    
    ggsave_pdf_safe(out_pdf_path, plt_out, width = 6.6, height = 4.0)
    
    if (isTRUE(emit_tikz)) {
      out_dir_tikz <- file.path("tex", "L_change", "fig_brokenx_tikz")
      dir.create(out_dir_tikz, recursive = TRUE, showWarnings = FALSE)
      out_tikz_name <- paste0(gsub("[^A-Za-z0-9]+","_", obj_name),
                              "_Nexp", Nexp_pick, "_Nobs", Nobs_pick, "_M", M_pick, "_brokenx_new2.tex")
      out_tikz_path <- file.path(out_dir_tikz, out_tikz_name)
      tikzDevice::tikz(file = out_tikz_path, width = 6.6, height = 4.0,
                       standAlone = isTRUE(tikz_standalone))
      print(plt_out)  # ← 合成済み（凡例付き）を出力
      grDevices::dev.off()
    }
  }
  
  # ----- ケース別（Exp / Obs / Both）の図：旧版踏襲 -----
  make_theta_lineplots_for_obj_brokenx_trans_case <- function(
    df_all, obj_name, case_pick,
    Nexp_pick = 1000, Nobs_pick = 1000, M_pick = 100,
    split_at = 0.85, width_left = 1, width_right = 3,
    right_major_by = 0.02, emit_tikz = FALSE, tikz_standalone = FALSE
  ){
    stopifnot(case_pick %in% c("exp","obs","both"))
    
    # --- LaTeXエスケープ（TikZ出力時のみ） ---
    latex_escape <- function(s) {
      if (!isTRUE(emit_tikz)) return(s)
      s <- gsub("([%_&#$])", "\\\\\\1", s, perl = TRUE)
      s
    }
    
    df1 <- df_all %>%
      dplyr::filter(Nexp == Nexp_pick, Nobs == Nobs_pick, M == M_pick, case == case_pick) %>%
      dplyr::select(theta, mean_lb, ci_lb_lo, ci_lb_hi, mean_ub, ci_ub_lo, ci_ub_hi, true) %>%
      dplyr::arrange(theta)
    if (nrow(df1) == 0L) return(invisible(NULL))
    
    true_vals <- df1 %>% dplyr::filter(is.finite(true)) %>% dplyr::distinct(true) %>% dplyr::pull(true)
    true_val  <- if (length(true_vals)) true_vals[1] else NA_real_
    
    thetas <- sort(unique(df1$theta)); if (!length(thetas)) thetas <- c(0, 1)
    
    # --- ここがポイント：凡例ラベルに含まれる % を必要時にエスケープ ---
    ci_core <- latex_escape("95% CI")
    lb_lab  <- paste0("LB (", ci_core, ")")
    ub_lab  <- paste0("UB (", ci_core, ")")
    
    plot_long <- dplyr::bind_rows(
      df1 %>% dplyr::transmute(theta, value = mean_lb, series = "LB"),
      df1 %>% dplyr::transmute(theta, value = mean_ub, series = "UB")
    ) %>% dplyr::filter(is.finite(theta), is.finite(value))
    
    plot_line <- plot_long %>%
      dplyr::group_by(series) %>%
      dplyr::filter(dplyr::n() >= 2) %>%
      dplyr::ungroup()
    
    rib_long <- dplyr::bind_rows(
      df1 %>% dplyr::transmute(theta, ymin = ci_lb_lo, ymax = ci_lb_hi, ci_series = lb_lab),
      df1 %>% dplyr::transmute(theta, ymin = ci_ub_lo, ymax = ci_ub_hi, ci_series = ub_lab)
    ) %>% dplyr::filter(is.finite(ymin), is.finite(ymax))
    
    true_long <- if (is.finite(true_val)) {
      tibble::tibble(theta = range(thetas), value = true_val, series = "True")
    } else tibble::tibble(theta = numeric(0), value = numeric(0), series = character(0))
    
    piecewise_x_trans <- function(split_at = 0.85, width_left = 1, width_right = 3) {
      stopifnot(split_at > 0, split_at < 1, width_left > 0, width_right > 0)
      r <- width_left / (width_left + width_right)
      fwd <- function(x) ifelse(x <= split_at, (r / split_at) * x, r + ((x - split_at) / (1 - split_at)) * (1 - r))
      inv <- function(u) ifelse(u <= r, (split_at / r) * u, split_at + ((u - r) / (1 - r)) * (1 - split_at))
      scales::trans_new(
        name = sprintf("piecewise_x_%.2f_%.2f_%.2f", split_at, width_left, width_right),
        transform = fwd, inverse = inv
      )
    }
    tr <- piecewise_x_trans(split_at, width_left, width_right)
    breaks_left  <- c(0, 0.50, split_at)
    breaks_right <- seq(split_at, 1.0, by = right_major_by)
    axis_breaks  <- sort(unique(c(breaks_left, breaks_right)))
    axis_labels  <- formatC(axis_breaks, format = "f", digits = 2)
    
    y_ci_vals <- c(rib_long$ymin, rib_long$ymax)
    y_all <- c(plot_long$value, true_long$value, y_ci_vals); y_all <- y_all[is.finite(y_all)]
    y_lim <- if (length(y_all)) {
      y_min <- min(y_all); y_max <- max(y_all); dy <- y_max - y_min; if (dy <= 0) dy <- 1e-6
      eps <- max(1e-9, 1e-6 * dy)
      c(y_min - 0.04*dy - eps, y_max + max(0.10*dy, 0.04) + eps)
    } else c(0, 1)
    
    points_plot <- plot_long %>%
      dplyr::filter(value >= y_lim[1], value <= y_lim[2])
    
    # タイトルも安全側に
    title_txt <- paste0(obj_name, " (", tools::toTitleCase(case_pick), ")")
    title_txt <- latex_escape(title_txt)
    
    plt <- ggplot2::ggplot() +
      ggplot2::geom_ribbon(data = rib_long,
                           ggplot2::aes(x = theta, ymin = ymin, ymax = ymax, fill = ci_series),
                           alpha = 0.22, show.legend = TRUE) +
      ggplot2::geom_line(data = plot_line,
                         ggplot2::aes(x = theta, y = value, linetype = series),
                         linewidth = 0.65, show.legend = TRUE) +
      ggplot2::geom_point(data = points_plot,
                          ggplot2::aes(x = theta, y = value, shape = series),
                          size = 1.9, stroke = 0.35, show.legend = TRUE, na.rm = TRUE) +
      ggplot2::geom_line(data = true_long,
                         ggplot2::aes(x = theta, y = value, linetype = series),
                         linewidth = 0.65, show.legend = TRUE) +
      ggplot2::scale_x_continuous(trans = tr, breaks = axis_breaks, labels = axis_labels,
                                  expand = ggplot2::expansion(mult = 0.001)) +
      ggplot2::coord_cartesian(ylim = y_lim, expand = FALSE) +
      ggplot2::labs(title = title_txt, x = "L", y = NULL) +
      ggplot2::theme_bw(base_size = 12) +
      ggplot2::theme(panel.grid.major = ggplot2::element_line(colour = "grey85", linewidth = 0.30),
                     panel.grid.minor = ggplot2::element_blank(),
                     legend.title = ggplot2::element_blank())
    
    # 保存（PDF）
    out_dir_pdf <- file.path("tex", "L_change", "fig_brokenx", "by_case")
    dir.create(out_dir_pdf, recursive = TRUE, showWarnings = FALSE)
    out_pdf_name <- paste0(gsub("[^A-Za-z0-9]+","_", obj_name),
                           "_Nexp", Nexp_pick, "_Nobs", Nobs_pick, "_M", M_pick,
                           "_brokenx_case-", case_pick, ".pdf")
    out_pdf_path <- file.path(out_dir_pdf, out_pdf_name)
    ggsave_pdf_safe(out_pdf_path, plt, width = 6.6, height = 4.0)
    
    # 保存（TikZ：必要時）
    if (isTRUE(emit_tikz)) {
      out_dir_tikz <- file.path("tex", "L_change", "fig_brokenx_tikz", "by_case")
      dir.create(out_dir_tikz, recursive = TRUE, showWarnings = FALSE)
      out_tikz_name <- sub("\\.pdf$", ".tex", out_pdf_name)
      out_tikz_path <- file.path(out_dir_tikz, out_tikz_name)
      tikzDevice::tikz(file = out_tikz_path, width = 6.6, height = 4.0,
                       standAlone = isTRUE(tikz_standalone))
      print(plt)
      grDevices::dev.off()
    }
  }
  
  
  # ---- 実行：全オブジェクトについて、メイン図＋ケース別図を出力 ----
  stopifnot(exists("RESULT_theta_summary"), is.data.frame(RESULT_theta_summary))
  objs_fig_bx <- unique(RESULT_theta_summary$obj)
  
  
  # --- TikZ 強制オン & 動作ログ ---
  DO_TIKZ <- TRUE
  TIKZ_STANDALONE <- FALSE
  suppressPackageStartupMessages(library(tikzDevice))
  
  message("[DEBUG] getwd() = ", getwd())
  message("[DEBUG] DO_TIKZ = ", DO_TIKZ)
  
  # 出力先フォルダを明示作成（両方）
  dir.create(file.path("tex","L_change","fig_brokenx_tikz"), recursive=TRUE, showWarnings=FALSE)
  dir.create(file.path("tex","L_change","fig_brokenx_tikz","by_case"), recursive=TRUE, showWarnings=FALSE)
  
  ## デバイスのスモークテスト（1回だけ）
  #tikz_test <- file.path("tex","L_change","fig_brokenx_tikz","__tikz_smoketest.tex")
  #tikzDevice::tikz(tikz_test, width=2, height=1.5, standAlone=FALSE)
  #plot(1:3, 1:3, type="l"); dev.off()
  #message("[DEBUG] tikz smoketest exists? ", file.exists(tikz_test))
  
  
  
  for (ob in objs_fig_bx) {
    df_ob <- dplyr::filter(RESULT_theta_summary, obj == ob)
    
    # 合成凡例付きのメイン図（PDF/TikZ）
    make_theta_lineplots_for_obj_brokenx_trans(
      df_ob, ob,
      Nexp_pick = 1000, Nobs_pick = 1000, M_pick = 100,
      split_at = 0.85, width_left = 1, width_right = 3, right_major_by = 0.02,
      show_obs = TRUE,
      emit_tikz = isTRUE(DO_TIKZ),
      tikz_standalone = if (exists("TIKZ_STANDALONE")) TIKZ_STANDALONE else FALSE
    )
    
    # ケース別（Exp/Obs/Both）図（PDF/TikZ）
    for (cs in c("exp","obs","both")) {
      make_theta_lineplots_for_obj_brokenx_trans_case(
        df_ob, ob, case_pick = cs,
        Nexp_pick = 1000, Nobs_pick = 1000, M_pick = 100,
        split_at = 0.85, width_left = 1, width_right = 3, right_major_by = 0.02,
        emit_tikz = isTRUE(DO_TIKZ),
        tikz_standalone = if (exists("TIKZ_STANDALONE")) TIKZ_STANDALONE else FALSE
      )
    }
  }
}

# ======================================================================
