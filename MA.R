###########################################################
#Author: Moritz Hafner 16-609-778                       ###  
#Context: script to download, clean HF data,            ###
#         build Multivariate Realized GARCH             ### 
#         forecast and evaluate it and                  ###
#         compare to CCC and DCC GARCH                  ###
#Master's Thesis in MiQEF                               ###
###########################################################
###libraries ####
library(data.table)
library(plyr)
library(dplyr)
library(RPostgres)
library(xts)
library(lubridate)
library(highfrequency)
library(mcompanion)
library(xtable)
library(stats4)
library(moments)
library(Matrix)
library(rugarch)
library(rmgarch)
library(corpcor)

#########functions #########

#function for cleaning step 7 
Q4 <- function(trades){
  bool <- list()
  bool <- rep(TRUE,length(trades$PRICE))
  for(i in 26:(length(trades$PRICE)-26)){
    
    bool[i] <- abs(trades$PRICE[i]-median(trades$PRICE[c(setdiff((i-25):(i+25),i))]))<
      10*mad(trades$PRICE[c(setdiff((i-25):(i+25),i))])
    
  }
  return(bool)}

#cleaning function
TradeCleanerTR <- function(trades){
  cleaned <- vector(length = 9)
  trades0 <- trades %>% 
    rename(DT = dt, PRICE = price, SYM_ROOT = sym_root, SYM_SUFFIX = sym_suffix, 
           SIZE = size, EX = ex, COND = tr_scond, CORR = tr_corr) %>%
    mutate(DT = lubridate::ymd_hms(DT, tz = "UTC")) %>%
    data.table::as.data.table()
  cleaned[1] <- length(trades0[[1]])
  #1 Delete entries with a time stamp outside the 
  # 9:30 am ??? 4 pm window when the exchange is open
  trades1 <- trades0 %>% exchangeHoursOnly()
  cleaned[2] <- length(trades0[[1]])- length(trades1[[1]])
  #2 Delete entries with a bid, ask or transaction price equal to zero
  trades2 <- trades1[trades1$PRICE != 0]
  cleaned[3] <- length(trades1[[1]])- length(trades2[[1]])
  #3 Retain entries originating from a single exchange. Delete other entries
  trades3 <- trades2 %>% selectExchange(c("N", "T", "Q"))
  cleaned[4] <- length(trades2[[1]])- length(trades3[[1]])
  #4 Delete entries with corrected trades. (Trades with a Correction Indicator, CORR != 0)
  trades4 <- trades3[trades3$CORR == "00"]
  cleaned[5] <- length(trades3[[1]])- length(trades4[[1]])
  #5 Delete entries with abnormal Sale Condition. 
  #  (Trades where COND has a letter code, except for ???E??? and ???F???)    
  trades5 <- trades4 %>% tradesCondition()
  cleaned[6] <- length(trades4[[1]])- length(trades5[[1]])
  #6 If multiple transactions have the same time stamp, use the median price.
  trades6 <- trades5 %>% mergeTradesSameTimestamp()
  cleaned[7] <- length(trades5[[1]])- length(trades6[[1]])
  #7  Delete entries for which the trade deviated by more than 10 mean absolute 
  #   deviations from a rolling centred median (excluding the observation under 
  #   consideration) of 50 observations (25 observations before and 25 after)
  trades7 <- trades6[Q4(trades6)==T]
  cleaned[8] <- length(trades6[[1]])- length(trades7[[1]])
  cleaned[9] <- length(trades6[[1]])
  return(trades6[,c(1,3)])
}

#cleaning function giving cleaning numbers
TradeCleanerCL <- function(trades){
  cleaned <- vector(length = 9)
  trades0 <- trades %>% 
    rename(DT = dt, PRICE = price, SYM_ROOT = sym_root, SYM_SUFFIX = sym_suffix, 
           SIZE = size, EX = ex, COND = tr_scond, CORR = tr_corr) %>%
    mutate(DT = lubridate::ymd_hms(DT, tz = "UTC")) %>%
    data.table::as.data.table()
  cleaned[1] <- length(trades0[[1]])
  #1 Delete entries with a time stamp outside the 
  # 9:30 am ??? 4 pm window when the exchange is open
  trades1 <- trades0 %>% exchangeHoursOnly()
  cleaned[2] <- length(trades0[[1]])- length(trades1[[1]])
  #2 Delete entries with a bid, ask or transaction price equal to zero
  trades2 <- trades1[trades1$PRICE != 0]
  cleaned[3] <- length(trades1[[1]])- length(trades2[[1]])
  #3 Retain entries originating from a single exchange. Delete other entries
  trades3 <- trades2 %>% selectExchange(c("N", "T", "Q"))
  cleaned[4] <- length(trades2[[1]])- length(trades3[[1]])
  #4 Delete entries with corrected trades. (Trades with a Correction Indicator, CORR != 0)
  trades4 <- trades3[trades3$CORR == "00"]
  cleaned[5] <- length(trades3[[1]])- length(trades4[[1]])
  #5 Delete entries with abnormal Sale Condition. 
  #  (Trades where COND has a letter code, except for ???E??? and ???F???)    
  trades5 <- trades4 %>% tradesCondition()
  cleaned[6] <- length(trades4[[1]])- length(trades5[[1]])
  #6 If multiple transactions have the same time stamp, use the median price.
  trades6 <- trades5 %>% mergeTradesSameTimestamp()
  cleaned[7] <- length(trades5[[1]])- length(trades6[[1]])
  #7  Delete entries for which the trade deviated by more than 10 mean absolute 
  #   deviations from a rolling centred median (excluding the observation under 
  #   consideration) of 50 observations (25 observations before and 25 after)
  trades7 <- trades6[Q4(trades6)==T]
  cleaned[8] <- length(trades6[[1]])- length(trades7[[1]])
  cleaned[9] <- length(trades6[[1]])
  return(cleaned)
}

#log of matrices
logmat <- function(a = matrix) {
  eav <- eigen(a)$values
  evec <- eigen(a)$vectors 
  leav <- log(eav)
  dleav <- diag(leav)
  lmat <- evec%*%dleav%*%t(evec)
  return(lmat)
}

#introduce block structure to a vector
block <- function(x = prices) {
  
  x[c(1,2,9)] <- mean(x[c(1,2,9)])
  x[c(3:5,10:12,16:18)] <- mean(x[c(3:5,10:12,16:18)])
  x[c(6:8,13:15,19:21)] <- mean(x[c(6:8,13:15,19:21)])
  x[c(22,23,27)] <- mean(x[c(22,23,27)])
  x[c(24:26,28:33)] <- mean(x[c(24:26,28:33)])
  x[c(34:36)] <- mean(x[c(34:36)])
  
  return(x)
}

#reverse the log of the matrix, taken from the mathlab code in the appendix of Archakov nd Hansen (2021)
logmatinv <- function(v = lower_tri, tol_value) {
  n = 0.5*(1+sqrt(1+8*length(v)))
  iter_number = -1
  G = matrix(0,n,n)
  G[lower.tri(G, diag=FALSE)] <- v
  G = G+t(G)
  diag_vec <- rep(1,9)
  conv <- max(sqrt(n), sqrt(n)*tol_value)
  while (conv > sqrt(n)*tol_value) {
    diag_delta = log(diag(expm(G)))
    diag_vec = diag_vec - diag_delta
    diag(G) = diag_vec
    conv = norm(as.matrix(diag_delta))
    iter_number = iter_number + 1
  }
  C = as.matrix(expm(G))
  return(C)
}

#get C, H, rho, ht from the MVR GARCH
get.ut <- function(theta, r, h, x, y, rho, N){
  omega <- theta[c(1:9)]
  beta <- diag(theta[c(10:18)])
  tau1 <- diag(theta[c(19:27)])
  tau2 <- diag(theta[c(28:36)])
  gamma <- diag(theta[c(37:45)])
  omegatilde <- theta[c(46:81)]
  betatilde <- diag(theta[c(82:117)])
  gammatilde <- diag(theta[c(118:153)])  
  xi <- theta[c(154:162)]
  phi <- diag(theta[c(163:171)])
  delta1 <- diag(theta[c(172:180)])
  delta2 <- diag(theta[c(181:189)])
  xitilde <- theta[c(190:225)]
  phitilde <- diag(theta[c(226:261)])
  
  #help variable
  mu <- rowMeans(r)
  rt <- r[,1:2]
  lx <- log(x); lxt <- lx[,1:2]
  yt <- y[,1:2]
  lht <- matrix(0, ncol = N, nrow = nrow(r))
  lht[,1] = log(h)
  zt <- matrix(0, ncol = N, nrow = nrow(r))
  rhot <- matrix(0, ncol = N, nrow = 36)
  rhot[,1] = rho
  Ct <- array(0,c(9,9,N))
  Ht <- array(0,c(9,9,N))
  Ct[,,1] = logmatinv(rhot[,1], 1e-8)
  Ht[,,1] = sqrt(diag(exp(lht[,1])))%*%Ct[,,1]%*%sqrt(diag(exp(lht[,1])))
  I <- rep(1,9)
  nu <- matrix(0, ncol = N, nrow = nrow(r))
  nutilde <-  matrix(0, ncol = N, nrow = 36)
  ut <- matrix(0, ncol = N, nrow = 45)
  #get u from estimation
  for (i in 2:N){
    #update param
    rt[,2] <- r[,i]; lxt[,2] <- lx[,i]; yt[,2] <- y[,i]
    #GARCH equations {h,rho,C}
    lht[,i] =  omega + beta%*%lht[,i-1] + tau1%*%zt[,1]+tau2%*%(zt[,1]*zt[,1]-I) + 
      gamma%*%lxt[,1]
    rhot[,i] = omegatilde + betatilde%*%rhot[,i-1] + gammatilde%*%yt[,1]
    Ct[,,i] = logmatinv(rhot[,i], 1e-8)
    Ht[,,i] = sqrt(diag(exp(lht[,i])))%*%Ct[,,i]%*%sqrt(diag(exp(lht[,i])))
    #measurement equations {z,u}
    zt[,i] = c((rt[,2]-mu)*exp(lht[,i])^(-0.5))
    nu[,i] = lxt[,2]-xi- phi%*%lht[,i]-(delta1%*%zt[,i]+delta2%*%(zt[,i]*zt[,i]-I))
    nutilde[,i] = yt[,2] - xitilde - phitilde%*%rhot[,i]
    ut[,i] <- c(nu[,i], nutilde[,i])
    #update params
    lht[,1] <- lht[,2]; zt[,1] <- zt[,2];
    rt[,1] <- rt[,2]; lxt[,1] <- lxt[,2]; yt[,1] <- yt[,2]
  }
  
  res <- list(lht, rhot, Ct, Ht, ut)
  names(res) <- c('lht', 'rhot', 'Ct', 'Ht', 'ut')
  
  return(res)
}

#forecast for the MVR GARCH
mvrforecast <- function(theta, r, u, Sigma, h, x, y, rho, C, H, k = horizon, boot = T){
  omega <- theta[c(1:9)]
  beta <- diag(theta[c(10:18)])
  tau1 <- diag(theta[c(19:27)])
  tau2 <- diag(theta[c(28:36)])
  gamma <- diag(theta[c(37:45)])
  omegatilde <- theta[c(46:81)]
  betatilde <- diag(theta[c(82:117)])
  gammatilde <- diag(theta[c(118:153)])  
  xi <- theta[c(154:162)]
  phi <- diag(theta[c(163:171)])
  delta1 <- diag(theta[c(172:180)])
  delta2 <- diag(theta[c(181:189)])
  xitilde <- theta[c(190:225)]
  phitilde <- diag(theta[c(226:261)])
  
  #bootstrap or sim r & bootstrap u
  mu <- rowMeans(r)
  if ( boot == T){
    rt <- r[,sample(11:train, k, replace = T)]
  } else {
    rt <- as.matrix(as.data.table(lapply(1:k, function(x) rnorm(9, sd = C))))
  }
  rt[,1] <- r[,train]
  
  ut <- u[,sample(111:train, k, replace = T)]
  
  nu <- ut[1:9,]
  nutilde <- ut[10:45,]
  
  #help variable
  lxt <- matrix(0, ncol = k, nrow = nrow(r))
  yt <- matrix(0, ncol = k, nrow = 36)
  lht <- matrix(0, ncol = k, nrow = nrow(r))
  zt <- matrix(0, ncol = 2, nrow = nrow(r))
  rhot <- matrix(0, ncol = k, nrow = 36)
  Ct <- array(0,c(9,9,k))
  Ht <- array(0,c(9,9,k))
  I <- rep(1,9)
  Rp <- numeric(k)
  Vp <- numeric(k)
  
  #loop GARCH and measurement equations through time
  #initialize params
  rz <- rt[,1]
  nuz <- nu[,1]
  nutildez <- nutilde[,1]
  lht[,1] <- h
  lxt[,1] <- log(x)
  yt[,1] <- y
  zt[,1] <- (rt[,1]-mu)*exp(lht[,1])^(-0.5)
  rhot[,1] <- rho
  Ct[,,1] <- C
  Ht[,,1] = H
  
  w <- rep(1/9,9)
  Rp <- c(); Rp[1] <- w%*%rt[,1]
  Vp <- c(); Vp[1] = t(w)%*%Ht[,,1]%*%w
  
  for (i in 2:k){
    #update params
    zt[,1] <- zt[,2]; rz <- rt[,i]; nuz <- nu[,i]; nutildez <- nutilde[,i]; 
    #GARCH equations {h,rho,C}
    lht[,i] =  omega + beta%*%lht[,i-1] + tau1%*%zt[,1]+tau2%*%(zt[,1]*zt[,1]-I) + gamma%*%lxt[,i-1]
    rhot[,i] = omegatilde + betatilde%*%rhot[,i-1] + gammatilde%*%yt[,i-1]
    Ct[,,i] = logmatinv(rhot[,i], 1e-8)
    Ht[,,i] = sqrt(diag(exp(lht[,i])))%*%Ct[,,i]%*%sqrt(diag(exp(lht[,i])))
    #measurement equations {z,u}
    zt[,2] = ifelse(boot == T, c((rz-mu)*exp(lht[,i])^(-0.5)), rz)
    lxt[,i] = xi + phi%*%lht[,i] + (delta1%*%zt[,2]+delta2%*%(zt[,2]*zt[,2]-I)) + nuz
    yt[,i]= xitilde + phitilde%*%rhot[,i] + nutildez
    
    #portfolio return and var
    Rp[i] <- w%*%rt[,i]
    Vp[i] <- t(w)%*%Ht[,,i]%*%w
    
  }
  #print(beta+gamma); print(betatilde+gammatilde*phitilde)
  res <- list(lht, Ct, rt, Ht, Rp, Vp)
  names(res) <- c('lht', 'Ct', 'rt', 'Ht', 'Rp', 'Vp')
  
  return(res)
}

#get C, H, zeta, ht from MVR Block GARCH
get.utb <- function(theta, r, h, x, y, zeta, N){
  omega <- theta[c(1:9)]
  beta <- diag(theta[c(10:18)])
  tau1 <- diag(theta[c(19:27)])
  tau2 <- diag(theta[c(28:36)])
  gamma <- diag(theta[c(37:45)])
  omegabar <- theta[c(46:51)]
  betabar <- diag(theta[c(52:57)])
  gammabar <- diag(theta[c(58:63)])  
  xi <- theta[c(64:72)]
  phi <- diag(theta[c(73:81)])
  delta1 <- diag(theta[c(82:90)])
  delta2 <- diag(theta[c(91:99)])
  xibar <- theta[c(100:105)]  
  phibar <- diag(theta[c(106:111)])
  
  #help variable
  mu <- rowMeans(r)
  rt <- r[,1:2]
  xt <- x[,1:2]
  yt <- y[,1:2]
  lht <- matrix(0, ncol = N, nrow = nrow(r))
  lht[,1] = log(h)
  zt <- matrix(0, ncol = N, nrow = nrow(r))
  zetat <- matrix(0, ncol = N, nrow = 6)
  zetat[,1] = zeta
  Ct <- array(0,c(9,9,N))
  Ht <- array(0,c(9,9,N))
  Ct[,,1] = logmatinv(A%*%zetat[,1], 1e-8)
  Ht[,,1] = sqrt(diag(exp(lht[,1])))%*%Ct[,,1]%*%sqrt(diag(exp(lht[,1])))
  I <- rep(1,9)
  nu <- matrix(0, ncol = N, nrow = nrow(r))
  nubar <-  matrix(0, ncol = N, nrow = 6)
  ut <- matrix(0, ncol = N, nrow = 15)
  #get u from estimation
  for (i in 2:N){
    #update param
    rt[,2] <- r[,i]; xt[,2] <- x[,i]; yt[,2] <- y[,i]
    #GARCH equations {h,rho,C}
    lht[,i] =  omega + beta%*%lht[,i-1] + tau1%*%zt[,1]+tau2%*%(zt[,1]*zt[,1]-I) + 
      gamma%*%log(xt[,1])
    zetat[,i] = omegabar + betabar%*%zetat[,i-1] + gammabar%*%yt[,1]
    Ct[,,i] = logmatinv(A%*%zetat[,i], 1e-8)
    Ht[,,i] = sqrt(diag(exp(lht[,i])))%*%Ct[,,i]%*%sqrt(diag(exp(lht[,i])))
    #measurement equations {z,u}
    zt[,i] = c((rt[,2]-mu)*exp(lht[,i])^(-0.5))
    nu[,i] = log(xt[,2])-xi- phi%*%lht[,i]-(delta1%*%zt[,i]+delta2%*%(zt[,i]*zt[,i]-I))
    nubar[,i] = yt[,2] - xibar - phibar%*%zetat[,i]
    ut[,i] <- c(nu[,i], nubar[,i])
    #update params
    lht[,1] <- lht[,2]; zt[,1] <- zt[,2];
    rt[,1] <- rt[,2]; xt[,1] <- xt[,2]; yt[,1] <- yt[,2]
  }
  
  res <- list(lht, zetat, Ct, Ht, ut)
  names(res) <- c('lht', 'zetat', 'Ct', 'Ht', 'ut')
  
  return(res)
}

#forecast for MVR Block GARCH
mvrbforecast <- function(theta, r, u, Sigma, h, x, y, zeta, C, H, k = horizon, boot = T){
  omega <- theta[c(1:9)]
  beta <- diag(theta[c(10:18)])
  tau1 <- diag(theta[c(19:27)])
  tau2 <- diag(theta[c(28:36)])
  gamma <- diag(theta[c(37:45)])
  omegabar <- theta[c(46:51)]
  betabar <- diag(theta[c(52:57)])
  gammabar <- diag(theta[c(58:63)])  
  xi <- theta[c(64:72)]
  phi <- diag(theta[c(73:81)])
  delta1 <- diag(theta[c(82:90)])
  delta2 <- diag(theta[c(91:99)])
  xibar <- theta[c(100:105)]
  phibar <- diag(theta[c(106:111)])
  
  #bootstrap or sim r & bootstrap u
  mu <- rowMeans(r)
  if ( boot == T){
    rt <- r[,sample(11:train, k, replace = T)]
  } else {
    rt <- as.matrix(as.data.table(lapply(1:k, function(x) rnorm(9, sd = C))))
  }
  rt[,1] <- r[,train]
  
  ut <- u[,sample(11:train, k, replace = T)]
  
  nu <- ut[1:9,]
  nubar <- ut[10:15,]
  
  #help variable
  lxt <- matrix(0, ncol = k, nrow = nrow(r))
  yt <- matrix(0, ncol = k, nrow = 6)
  lht <- matrix(0, ncol = k, nrow = nrow(r))
  zt <- matrix(0, ncol = 2, nrow = nrow(r))
  zetat <- matrix(0, ncol = k, nrow = 6)
  Ct <- array(0,c(9,9,k))
  Ht <- array(0,c(9,9,k))
  I <- rep(1,9)
  Rp <- numeric(k)
  Vp <- numeric(k)
  
  #loop GARCH and measurement equations through time
  #initialize params
  rz <- rt[,1]
  nuz <- nu[,1]
  nubarz <- nubar[,1]
  lht[,1] <- h
  lxt[,1] <- log(x)
  yt[,1] <- y
  zt[,1] <- (rt[,1]-mu)*exp(lht[,1])^(-0.5)
  zetat[,1] <- zeta
  Ct[,,1] <- C
  Ht[,,1] = H
  
  w <- rep(1/9,9)
  Rp <- c(); Rp[1] <- w%*%rt[,1]
  Vp <- c(); Vp[1] = t(w)%*%Ht[,,1]%*%w
  
  for (i in 2:k){
    #update params
    rz <- rt[,i]; nuz <- nu[,i]; nubarz <- nubar[,i]; zt[,1] <- zt[,2]
    #GARCH equations {h,zeta,C}
    lht[,i] =  omega + beta%*%lht[,i-1] + tau1%*%zt[,1]+tau2%*%(zt[,1]*zt[,1]-I) + gamma%*%lxt[,i-1]
    zetat[,i] = omegabar + betabar%*%zetat[,i-1] + gammabar%*%yt[,i-1]
    Ct[,,i] = logmatinv(A%*%zetat[,i], 1e-8)
    Ht[,,i] = sqrt(diag(exp(lht[,i])))%*%Ct[,,i]%*%sqrt(diag(exp(lht[,i])))
    #measurement equations {z,u}
    zt[,2] = ifelse(boot == T, c((rz-mu)*exp(lht[,i])^(-0.5)), rz)
    lxt[,i] = xi + phi%*%lht[,i] + (delta1%*%zt[,2]+delta2%*%(zt[,2]*zt[,2]-I)) + nuz
    yt[,i]= xibar+ phibar%*%zetat[,i] + nubarz
    #portfolio return and var
    Rp[i] <- w%*%rt[,i]
    Vp[i] <- t(w)%*%Ht[,,i]%*%w
  }
  
  res <- list(lht, Ct, rt, Ht, Rp, Vp)
  names(res) <- c('lht', 'Ct', 'rt', 'Ht', 'Rp', 'Vp')
  
  return(res)
}

#indicator function to evaluate forecasts
eval.fcst <- function(fcr = fcreturn, fcv = fcvola, a = normqu, p = qupercent, k = horizon, N = numb.of.sim) {
  
  var <- rowMeans(fcr)-a*sqrt(rowMeans(fcv)) #forecast
  es <- rowMeans(fcr) - sqrt(rowMeans(fcv))*(dnorm(a)/(p)) #forecast
  vvar <- matrix(0,k,N)
  for (i in 1:k) {
    for (j in 1:N) {
      if (fcr[i,j] < var[i]) {
        vvar[i,j] = 1
      } else {
        vvar[i,j] = 0
      }
    }}
  
  ees <- vvar*fcr
  
  vvar <- rowSums(vvar)/N - p #indicator function var
  ves <- -rowSums(ees)/(p*N) + es #indicator function es
  
  res <- list(var, vvar, ves, es)
  names(res) <- c('var', 'vvar', 'ves', 'es')
  return(res)
  
}

#forecast function DCC
DCCforecast <- function(omega, alpha, beta, sigma2tm1, a, b, Q, R, H, nu, h = horizon, r, boot = T){
  #define
  if ( boot == T){
    rt <- r[,sample(11:train, h, replace = T)]-mu
  } else {
    rt <- as.matrix(as.data.table(lapply(1:h, function(x) rnorm(9, sd = sqrt(sigma2tm1)))))
  }
  
  rt[,1] <- r[,train]
  
  sigma2 <- array(0, c(9,h))
  sigma2[,1] = sigma2tm1^2
  
  Dt <- array(0,c(9,9,h))
  Dt[,,1] = diag(sqrt(sigma2[,1]))
  
  nut <- array(0,c(9,h))
  nut[,1] = nu
  
  Qbar <- array(0,c(9,9,h))
  Qbar[,,1] <- nut[,1]%*%t(nut[,1])
  Qbars <- array(0, c(9,9,1))
  
  Qt <- array(0,c(9,9,h))
  Qt[,,1] = Q
  
  Qtilde <- array(0, c(9,9,h))
  Qtilde[,,1] = diag(Qt[,,1])
  
  Rt <- array(0,c(9,9,h))
  Rt[,,1] = R
  
  Ht<- array(0,c(9,9,h))
  Ht[,,1] = Dt[,,1]%*%Rt[,,1]%*%Dt[,,1]
  
  #portfolio inputs
  w <- rep(1/9,9)
  Rp <- c(); Rp[1] <- w%*%rt[,1]
  Vp <- c(); Vp[1] = t(w)%*%Ht[,,1]%*%w
  
  # forecast
  for (t in 2:h) {
    sigma2[,t] = omega+alpha*rt[,t-1]^2+beta*sigma2[,t-1]
    Dt[,,t] = diag(sqrt(sigma2[,t]))
    nut[,t] = pseudoinverse(Dt[,,t], 1e-8)%*%rt[,t]
    Qbar[,,t] = nut[,t]%*%t(nut[,t])
    Qbars = rowMeans(Qbar[,,1:t], dims = 2)
    Qt[,,t] = Qbars*(1-a-b)+a*(nut[,t-1]%*%t(nut[,t-1])+b*Qt[,,t-1])
    Qtilde[,,t] = diag(Qt[,,t])
    Rt[,,t]= pseudoinverse(Qtilde[,,t], 1e-8)%*%Qt[,,t]%*%pseudoinverse(Qtilde[,,t], 1e-8)
    Ht[,,t]= Dt[,,t]%*%Rt[,,t]%*%Dt[,,t]
    
    #portfolio return
    Rp[t] <- w%*%rt[,t]
    Vp[t] <- t(w)%*%Ht[,,t]%*%w
  }
  
  res <- list(Ht,Rt,Qt,Qbar,nut,Dt,sigma2,rt,Rp,Vp)
  names(res) <- c('Ht','Rt','Qt','Qbar','nut','Dt','sigma2','rt','Rp','Vp')
  
  return(res)
}

#forecast functiuon CCC
CCCforecast <- function(omega, alpha, beta, sigma2tm1, R, H, h = horizon, r, boot){
  #define
  if ( boot == T){
    rt <- r[,sample(11:train, h, replace = T)]-mu
  } else { 
    rt <- as.matrix(as.data.table(lapply(1:h, function(x) rnorm(9, sd = sqrt(sigma2tm1)))))
  }
  rt[,1] <- r[,train]
  
  sigma2 <- array(0, c(9,h))
  sigma2[,1] = sigma2tm1^2
  
  Dt <- array(0,c(9,9,h))
  Dt[,,1] <- diag(sqrt(sigma2[,1]))
  
  Ht <- array(0,c(9,9,h))
  Ht[,,1] = H
  
  w <- rep(1/9,9)
  Rp <- c(); Rp[1] <- w%*%rt[,1]
  Vp <- c(); Vp[1] = t(w)%*%Ht[,,1]%*%w
  #forecast
  for (t in 2:h) {
    sigma2[,t] = omega+alpha*rt[,t-1]^2+beta*sigma2[,t-1] 
    Dt[,,t] = diag(sqrt(sigma2[,t]))
    Ht[,,t] = Dt[,,t]%*%R%*%Dt[,,t]
    
    #portfolio return
    Rp[t] <- w%*%rt[,t]
    
    Vp[t] <- t(w)%*%Ht[,,t]%*%w
  }
  
  #results
  res <- list(Ht,Dt,sigma2,Rp,Vp)
  names(res) <- c("Ht","Dt","sigma2","Rp","Vp")
  
  return(res)
  
}


#### connenction to wrds ####
wrds <- dbConnect(Postgres(), 
                  host='wrds-pgdata.wharton.upenn.edu',
                  port=9737,
                  sslmode='require',
                  dbname='wrds',
                  user='mohafner',
                  password = "******"
)

#### get dates ####
res <- dbSendQuery(wrds, "select distinct table_name
                   from information_schema.columns
                   where table_schema='taqmsec'
                   order by table_name")

df_dates <- dbFetch(res, n = -1)

dates_trades <-
  df_dates %>%
  filter(grepl("ctm",table_name), !grepl("ix_ctm",table_name)) %>%
  mutate(table_name = substr(table_name, 5, 12)) %>%
  unlist()

stock_a <- c("CVX", "MRO", "OXY", "JNJ", "LLY", "MRK", "AAPL", "MU", "ORCL")
stock_b <- c("AMZN", "AAPL", "MSFT", "BP", "XOM", "OXY", "TGT", "WMT", "BBY")

#### get daily data, clean, refresh and corrmat #####
#dd <- dates_trades[c(:3853,3855:3858, 3860:3951, 3953:3966, 3968:4011, 4013:4156, 4158:4284)])]
covmattest <- list()
corrmattest <- list()
#
dd <- dates_trades[c(1:10)]
all_stock <- list()

for (d in 1:length(dd)){
  for (i in 1:length(stock_b)) {
    stock <- stock_b[i]
    res <- dbSendQuery(wrds,
                       paste0("select concat(date, ' ',time_m) as DT,", 
                              " ex, sym_root, sym_suffix, price, size, tr_scond, tr_corr",
                              " from taqmsec.ctm_", dd[d], 
                              " where sym_root = '", stock, "'"
                       ))
    all_stock[[i]] <- dbFetch(res, n = -1)
    dbClearResult(res)
  }
  names(all_stock) <- stock_b
  print(d)
  #### Barndorff-Nielsen et al (2009) cleaning ####
  #df to store the cleaning process
  clean_stock <- lapply(all_stock, TradeCleanerTR)
  # cleaned <- as.data.frame(lapply(all_stock, TradeCleanerCL))
  # write.table(cleaned,"cleanedx.csv",append = T,sep = ",",row.names = T,col.names = F)
  
  print(d)
  #merge the single stock dfs to one with the refresh time approach 
  # by Barndorff-Nielsen et al. (2011) 
  merfresh <- refreshTime(clean_stock)
  
  #get realized cov matrix per day and aggregate to 5 min steps
  covmatpar5[[d]] <- rKernelCov(merfresh, cor = F, alignBy = "minutes", alignPeriod = 5, makeReturns = T,
                                kernelType = "Parzen", kernelParam = 0.97)
  corrmatpar5[[d]] <- rKernelCov(merfresh, cor = T, alignBy = "minutes", alignPeriod = 5, makeReturns = T,
                                 kernelType = "Parzen", kernelParam = 0.97)
  write.table(merfresh,"merged_stockpar5.csv",append = T,sep = ",",row.names = F,col.names = F)
  write.table(merfresh[length(merfresh$DT)],"closing_pricepar5.csv",append = T,sep = ",",
              row.names = F,col.names = F)
  print(d)
  
  names(covmatpar5)[[d]] <- dd[d]
  names(corrmatpar5)[[d]] <- dd[d]
  
}

### get intraday prices in one mat ####
merg <- as.data.frame(matrix(data = NA, nrow = 1, ncol = 10))
colnames(merg) <- c("DT", stock_b)
for (d in 1:length(dd)){
  for (i in 1:length(stock_b)) {
    stock <- stock_b[i]
    res <- dbSendQuery(wrds,
                       paste0("select concat(date, ' ',time_m) as DT,", 
                              " ex, sym_root, sym_suffix, price, size, tr_scond, tr_corr",
                              " from taqmsec.ctm_", dd[d], 
                              " where sym_root = '", stock, "'"
                       ))
    all_stock[[i]] <- dbFetch(res, n = -1)
    dbClearResult(res)
  }
  names(all_stock) <- stock_b
  print(d)
  #### Barndorff-Nielsen et al (2009) cleaning ####
  #df to store the cleaning process
  clean_stock <- lapply(all_stock, TradeCleanerTR)
  # cleaned <- as.data.frame(lapply(all_stock, TradeCleanerCL))
  # write.table(cleaned,"cleanedx.csv",append = T,sep = ",",row.names = T,col.names = F)
  
  print(d)
  #merge the single stock dfs to one with the refresh time approach 
  # by Barndorff-Nielsen et al. (2011) 
  merfresh <- refreshTime(clean_stock)
  if (d==1){
    merg <- merfresh
  } else {
    merg <- rbind(merg, merfresh)
  }
}
rRVar(merfresh, alignBy = "minutes", alignPeriod = 5, makeReturns = T)

tail(read.csv("merged_stock.csv"))
read.csv("cleaned.csv")

## returns with daily closing prices ####

CRSP <- read.csv("/Users/Moritz/Documents/MA/estimation_data/CRSP.csv")
CRSP <- split(CRSP, CRSP$TICKER)
CRSP <- lapply(CRSP, function(x) x[,-c(1,3,4)])
#CRSPr <- lapply(CRSPr, function(x) cbind(x, makeReturns(as.matrix(x))))
#CRSPr <- lapply(CRSPr, function(x) x[,-3])
CRSPdat <- as.Date(CRSP[[1]][[1]])
CRSP <- lapply(CRSP, function(x) x[,2])
clret <- data.frame(CRSP[[stock_b[1]]],CRSP[[stock_b[2]]],CRSP[[stock_b[3]]],
                    CRSP[[stock_b[4]]],CRSP[[stock_b[5]]],CRSP[[stock_b[6]]],
                    CRSP[[stock_b[7]]],CRSP[[stock_b[8]]],CRSP[[stock_b[9]]])
colnames(clret) <- stock_b
clr <- t(clret[-c(1:10),])

summary(clret)
retmoment <- matrix(data = 0, nrow = 3, ncol = 9)
for(i in 1:9){retmoment[1,i] <- sqrt(var(clret[,i]))}
for(i in 1:9){retmoment[2,i] <- skewness(clret[,i])}
for(i in 1:9){retmoment[3,i] <- kurtosis(clret[,i])}

plot(CRSPdat,clret$MSFT, type = 'l', xlab = "Time", ylab = "Return", main = "Return Time Series for MSFT")
hist(clret$MSFT, xlab = "Daily Return", breaks = 50, main = 'Daily Return Distribution for MSFT')

#### covariance and correlation ####

corrmat <- read.csv('/Users/Moritz/Documents/MA/corrmatfin.csv')
corrmat <- split(corrmat, rep(1:(length(corrmat[[1]])/9), each = 9))
covmat <- read.csv('/Users/Moritz/Documents/MA/covmatfin.csv')
covmat <- split(covmat, rep(1:(length(covmat[[1]])/9), each = 9))
logcorr <- lapply(corrmat, logmat)
logcov <- lapply(covmat, logmat)

##for plots ##
veccorr <- lapply(corrmat, function(x) x[lower.tri(x)])
veccorrdf <- matrix(NA, nrow = length(veccorr), ncol = 36)
for (i in 1:length(veccorr)) {
  veccorrdf[i,] <- veccorr[[i]]
}
veccorrdf <- as.data.frame(veccorrdf)

veccov <- lapply(covmat, function(x) x[lower.tri(x)])
veccovdf <- matrix(NA, nrow = length(veccov), ncol = 36)
for (i in 1:length(veccov)) {
  veccovdf[i,] <- veccov[[i]]
}
veccovdf <- as.data.frame(veccovdf)

#### vectorize lower triangle ####
y <- lapply(logcorr, function(x) x[lower.tri(x)])
y <- y[-c(1:10)]
ydf <- matrix(NA, nrow = length(y), ncol = 36)
for (i in 1:length(y)) {
  ydf[i,] <- y[[i]]
}
ydf <- as.data.frame(ydf)
RM <- lapply(logcov, function(x) x[lower.tri(x)])
RM <- RM[-c(1:10)]
RMdf <- as.data.frame(as.data.table(RM))
x <- lapply((logcov), diag)
x <- x[-c(1:10)]
xdf <- matrix(NA, nrow = length(y), ncol = 9)
for (i in 1:length(x)) {
  xdf[i,] <- x[[i]]
}
xdf <- as.data.frame(xdf)


plot(CRSPdat, veccovdf[,1], type = 'l')
plot(CRSPdat[-c(1:10)], xdf[1,], type = 'l')
plot(CRSPdat, veccorrdf[,35], type = 'l', xlab = "Time", ylab = "Corr(BBY,TGT)"
     , main = "Realized Correlation between BBY and TGT")
plot(CRSPdat[-c(1:10)], ydf[35,], type = 'l', xlab = "Time", ylab = "LogCorr(BBY,TGT)",
     main = "Paramterized Correlation between BBY and TGT")

### block structure ####
A <- matrix(data = 0, nrow = 36, ncol = 6)
A[c(1,2,9),1] = 1
A[c(3:5,10:12,16:18),2] = 1
A[c(6:8,13:15,19:21),3] = 1
A[c(22,23,27),4] = 1
A[c(24:26,28:33),5] = 1
A[c(34:36),6] = 1

#####load data for estimation and forecast if necessary and prepare it######
xdf <- read.csv("/Users/Moritz/Documents/MA/estimation_data/xdf.csv")
xdf <- t(xdf[,-1])
ydf <- read.csv("/Users/Moritz/Documents/MA/estimation_data/ydf.csv")
ydf <- t(ydf[,-1])

h <- diag(cov(clret))
rho <- logmat(cor(clret))[lower.tri(logmat(cor(clret)))]
zeta <- unique(block(rho))

#split between train and test set
train <- round(nrow(clret)*0.8)

## logmatreverse from Archakov&Lunde (2020)
A <- matrix(data = 0, nrow = 36, ncol = 6)
A[c(1,2,9),1] = 1
A[c(3:5,10:12,16:18),2] = 1
A[c(6:8,13:15,19:21),3] = 1
A[c(22,23,27),4] = 1
A[c(24:26,28:33),5] = 1
A[c(34:36),6] = 1

yblock <- lapply(y, function(x) block(x))

ybar <- list()
for (i in 1:length(yblock)){
  ybar[[i]] <- unique(yblock[[i]])
}

ybar <- as.matrix(as.data.table(ybar))

### estimate CCC anc DCC GARCH with rmgarch package ####
### DCC GARCH 
### with rugarch/rmgarch package ###
uspecDCC = multispec(replicate(9, ugarchspec(mean.model = list(armaOrder = c(1,0)))))

multDCC = multifit(uspecDCC, as.data.frame(t(clr[,1:train])))

specDCC = dccspec(uspec = uspecDCC, dccOrder = c(1,1), distribution = 'mvnorm')

DCC = dccfit(specDCC, data = as.data.frame(t(clr[,1:train])),
             fit.control = list(eval.se = T), fit = multDCC)

# cov1 = rcov(DCC)
# cor1 = rcor(DCC)

#### CCC GARCH
### estimate with rugarch package ###
uspecCCC = multispec(replicate(9, ugarchspec(mean.model = list(armaOrder = c(1,0)))))

multCCC = multifit(uspecCCC, as.data.frame(t(clr[,1:train])))

specCCC = cgarchspec(uspec = uspecCCC, dccOrder = c(1,1), distribution.model = list('mvnorm'))

CCC = cgarchfit(specCCC, data = as.data.frame(t(clr[,1:train])),
                fit.control = list(eval.se = T, stationarity = T), fit = multCCC )

# cov2 = rcov(CCC)
# cor2 = rcor(CCC)


#### forecasting risk measure ####
#### equiweighted portfolio for evaluation of measurements
equiport = c()
for (i in 1:4268){
  equiport[i] = w%*%clr[,i]
}

equivar  = var(equiport)
equimean = mean(equiport)
equiprob  = (equiport-equimean)/sqrt(equivar)

set.seed(121221)

#realized normal GARCH parameters taken form the estimation done with python
theta.norm <- c(9.93632914e-02,  1.00782022e-01,  1.00603469e-01,  1.02034642e-01,
                1.00268719e-01,  1.01170834e-01,  1.01180647e-01,  9.89156575e-02,
                1.01081043e-01,  6.58849156e-01,  6.79967576e-01, 6.92147044e-01,
                6.77849936e-01,  6.93051925e-01,  6.95534088e-01,  6.96529322e-01,
                6.95003841e-01,  6.87416458e-01,  5.59926216e-04, -4.26221113e-03,
                4.29987197e-03, -2.15635170e-03, -5.87619665e-03, -3.72537822e-04,
                -1.11608582e-03, -2.78297323e-04,  7.05119188e-04,  4.76874125e-02,
                1.58705783e-02,  6.78264989e-03,  1.98327389e-02,  1.13114664e-02,
                -1.22236781e-03,  7.63366034e-03,  1.16556650e-02,  1.98209741e-03,
                3.06021612e-01,  2.90979943e-01,  2.97954488e-01,  2.92177740e-01,
                2.97669813e-01,  2.99633131e-01,  2.98427610e-01,  3.03527536e-01,
                2.94147830e-01,  8.57612452e-03, 1.78048587e-02, 2.08177216e-02,
                -4.27151753e-04,  7.73226714e-03,  4.13828047e-03,  4.96824535e-04,
                -6.08945359e-07,  6.40021994e-03,  6.27418429e-02,  2.03710119e-03,
                1.17390413e-02,  3.94792488e-03,  5.77982231e-02,  7.55453080e-02,
                4.18723520e-03, -3.12252631e-03, 8.39970673e-03, -3.80022774e-03,
                -4.74186537e-03, -6.69932116e-03, -3.16734713e-02, -2.80349343e-02,
                1.05078973e-02, -5.95546030e-03,  5.27255193e-03, -4.86973600e-02,
                4.56637786e-02,  5.87487196e-03,  1.35322112e-02,  1.11117310e-02,
                5.23357860e-03,  2.89834108e-03, -2.40664694e-02,  1.54682093e-02,
                1.09698914e-02,  8.96631904e-01,  8.96795864e-01,  8.94115593e-01,
                8.93749876e-01,  8.94860422e-01,  8.95905148e-01,  8.93008076e-01,
                8.93414365e-01,  8.91363898e-01,  8.78456635e-01,  8.93255235e-01,
                8.94599420e-01,  8.95780111e-01,  8.84185417e-01,  8.82520204e-01,
                8.95423608e-01,  8.93828540e-01,  8.93017495e-01,  8.90787364e-01,
                8.91331636e-01,  8.89687064e-01,  8.77774830e-01,  8.78771649e-01,
                8.95360946e-01,  8.91654049e-01,  8.94461251e-01,  8.54971519e-01,
                8.89017568e-01,  8.92313973e-01,  8.93619213e-01,  8.94350071e-01,
                8.94059813e-01,  8.93392280e-01,  8.83364981e-01,  8.96753294e-01,
                8.98626299e-01,  8.53196793e-02,  8.08000150e-02,  7.65037234e-02,
                7.55963947e-02,  7.68914792e-02,  7.87322067e-02,  7.46592471e-02,
                7.75454633e-02,  7.87549263e-02,  7.73911128e-02,  7.80999630e-02,
                7.40908104e-02,  7.78953740e-02,  7.84678974e-02,  7.61078727e-02,
                7.93984964e-02,  7.75435885e-02,  7.65674339e-02,  7.31883523e-02,
                7.36934441e-02,  7.39859753e-02,  7.93365969e-02,  7.73909624e-02,
                7.86103507e-02,  7.65072781e-02,  7.74757042e-02,  6.75061481e-02,
                7.60872079e-02,  7.58587186e-02,  7.48310423e-02,  7.53323098e-02,
                7.52127550e-02,  7.61179969e-02, 7.39236508e-02, 8.51323981e-02,
                8.00617424e-02, -2.00450434e-01, -2.00929334e-01, -2.01363992e-01,
                -2.01716391e-01, -2.01711941e-01, -2.00507055e-01, -2.00190342e-01,
                -2.02378082e-01, -2.01769891e-01,  2.69576546e-01,  2.72601946e-01,
                2.71285224e-01,  2.86910655e-01,  2.76549651e-01,  2.81076166e-01,
                2.73474878e-01,  2.71532558e-01, 2.76289245e-01, -6.35297067e-04,
                -8.00812398e-03,  8.68333355e-03, -2.80468889e-04, -6.47102094e-03,
                2.42185662e-04,  6.45640473e-03,  5.61751532e-03,  3.02900883e-03,
                -8.71598447e-03,  4.81379749e-02,  2.78371924e-02,  4.98934703e-02,
                4.80653129e-02,  4.53821391e-02,  4.57620263e-02,  4.18519581e-02,
                3.88924101e-02,  5.39017891e-04,  1.72385461e-04, -4.98022778e-04,
                -1.04640428e-04, -1.62197105e-04,  1.88314463e-05,  2.80646712e-05,
                -1.28580457e-04,  9.04733191e-04, -1.93462445e-03,  5.48652412e-04,
                -1.63488275e-04,  3.07232941e-04, -2.00432106e-03, -2.14417101e-03,
                2.99509751e-04,  7.27269277e-04, -7.97551942e-06, -1.63097209e-04,
                1.18769213e-04,  5.01024886e-05,  2.71570736e-03,  2.18462318e-03,
                -3.60668826e-04,  9.14845145e-04,  4.67403080e-04,  2.64937858e-03,
                -1.35602508e-03,  1.41155345e-04, -1.19496149e-04, -9.21755411e-05,
                -9.96513480e-05,  2.94877898e-04,  1.73097949e-03, -3.62624777e-04,
                1.97195934e-04,  9.99221829e-01,  9.98755615e-01,  9.98381094e-01,
                9.98733856e-01,  9.98778351e-01,  9.98959843e-01,  9.98719098e-01,
                9.98916695e-01,  9.99042109e-01,  9.96475236e-01,  9.98957108e-01,
                9.98425193e-01,  9.98889449e-01,  9.97206493e-01,  9.96014814e-01,
                9.99097277e-01,  9.99098507e-01,  9.98746923e-01,  9.98624412e-01,
                9.98743861e-01,  9.98754728e-01,  1.00087342e+00,  1.00041636e+00,
                9.98943086e-01,  9.98829894e-01,  9.98980844e-01,  1.00053224e+00,
                9.97823363e-01,  9.98782933e-01,  9.98559434e-01,  9.98736140e-01,
                9.98722735e-01,  9.98851950e-01,  9.99753095e-01,  9.98592919e-01,
                9.98780251e-01)

  
MVRNpara <- get.ut(theta = theta.norm, r = clr, x = xdf, y = ydf, h = h, rho = rho, N = train)



#MVRN bootstrap forecast for 252 days 1000 times
MVRNbfr <- matrix(0,252,1000)
MVRNbfv <- matrix(0,252,1000)
for (i in 1:1000){
  temp <- mvrforecast(theta.norm, clr, MVRNpara$ut, Sigma, h = MVRNpara$lht[,train], 
                      x = xdf[,train], y = ydf[,train],
                      rho = MVRNpara$rhot[,train], C = MVRNpara$Ct[,,train], H = MVRNpara$Ht[,,train],
                      k = 252, boot = T)
  MVRNbfr[,i] <- temp$Rp
  MVRNbfv[,i] <- temp$Vp
  print(i)
  
}

#MVRN simulate forecast for 252 days 1000 times
MVRNsfr <- matrix(0,252,1000)
MVRNsfv <- matrix(0,252,1000)
for (i in 1:1000){
  temp <- mvrforecast(theta.norm, clr, MVRNpara$ut, Sigma, h = MVRNpara$lht[,train], 
                      x = xdf[,train], y = ydf[,train],
                      rho = MVRNpara$rhot[,train], C = MVRNpara$Ct[,,train], H = MVRNpara$Ht[,,train],
                      k = 252, boot = F)
  MVRNsfr[,i] <- temp$Rp
  MVRNsfv[,i] <- temp$Vp
  print(i)
  
}

#realized block GARCH parameters taken form the estimation done with python
theta.block <- c(1.01505154e-01,  1.01684250e-01,  1.01214193e-01,  1.01687593e-01,
                 1.00623592e-01,  1.01017515e-01,  1.00602998e-01,  1.00479086e-01,
                 1.01105984e-01,  6.68659261e-01,  6.79390662e-01,  6.87293791e-01,
                 6.81407393e-01,  6.94092681e-01,  6.90406742e-01,  6.93873467e-01,
                 6.92912716e-01,  6.84649317e-01,  3.22832925e-04, -7.40223827e-04,
                 1.14547952e-03, -6.76005323e-04, -9.69239113e-04, -3.73571864e-04,
                 -2.12372396e-04, -1.07958769e-04, -1.07919039e-03,  1.81652410e-02,
                 4.55761891e-03,  9.16500361e-04,  5.32853425e-03,  2.01803990e-03,
                 6.75041811e-05,  1.92276113e-03,  1.95755024e-03,  1.42475393e-03,
                 2.84673283e-01,  2.81974055e-01,  2.88694230e-01,  2.84539466e-01,
                 2.94029773e-01,  2.90724077e-01,  2.94342994e-01,  2.93587708e-01,
                 2.88257854e-01,  1.74571390e-02,  1.53664069e-02,  1.25056701e-02,
                 -5.51891462e-02,  6.96126058e-03,  1.09249540e-03,  9.03379854e-01,
                 9.03463274e-01,  8.97226436e-01,  8.56764697e-01,  9.02571863e-01,
                 8.98695597e-01,  9.56575137e-02,  8.73294789e-02,  8.54605393e-02,
                 7.74887597e-02,  8.78736173e-02,  9.01738396e-02, -2.00020965e-01,
                 -2.00261013e-01, -2.00355134e-01, -2.00492846e-01, -2.00512169e-01,
                 -2.00113078e-01, -2.00084145e-01, -2.00742742e-01, -2.00502362e-01,
                 1.06414173e-01,  1.07356105e-01,  1.06998528e-01,  1.10978604e-01,
                 1.09014127e-01,  1.09941749e-01,  1.08219028e-01,  1.06932241e-01,
                 1.08027435e-01, -1.20966382e-03, -2.17268289e-03,  2.37583884e-03,
                 -5.98629203e-05, -1.69005143e-03,  1.09045792e-04,  1.60128828e-03,
                 1.13190424e-03, -4.10132309e-05,  2.02034499e-02,  4.96584628e-02,
                 4.25791884e-02,  4.91256259e-02,  5.09479413e-02,  4.87061099e-02,
                 5.11095305e-02,  4.48289957e-02,  3.94710394e-02,  5.15268944e-04,
                 -1.09873265e-03, -1.31135562e-03,  3.15027599e-03, -4.67813745e-04,
                 6.72149076e-04,  9.99975606e-01,  9.99171472e-01,  9.99014777e-01,
                 1.00081279e+00,  9.99616672e-01,  9.99984674e-01)

MVRbpara <- get.utb(theta = theta.block, r = clr, x = xdf, y = ybar, h = h, zeta = zeta, N = train)

#MVRb bootstrap forecast for 252 days 1000 times
MVRbbfr <- matrix(0,252,1000)
MVRbbfv <- matrix(0,252,1000)
for (i in 1:1000){
  temp <- mvrbforecast(theta.block, clr, MVRbpara$ut, h = MVRbpara$lht[,train],
                      x = xdf[,train], y = ybar[,train],
                      zeta = MVRbpara$zetat[,train], C = MVRbpara$Ct[,,train],
                      H = MVRbpara$Ht[,,train], k = 252, boot = T)
  MVRbbfr[,i] <- temp$Rp
  MVRbbfv[,i] <- temp$Vp
  print(i)
  
}

#MVRN simulate forecast for 252 days 1000 times
MVRbsfr <- matrix(0,252,1000)
MVRbsfv <- matrix(0,252,1000)
for (i in 1:1000){
  temp <- mvrbforecast(theta.block, clr, MVRbpara$ut, h = MVRbpara$lht[,train],
                       x = xdf[,train], y = ybar[,train],
                       zeta = MVRbpara$zetat[,train], C = MVRbpara$Ct[,,train],
                       H = MVRbpara$Ht[,,train], k = 252, boot = F)
  MVRbsfr[,i] <- temp$Rp
  MVRbsfv[,i] <- temp$Vp
  print(i)
  
}

#DCC
#get estimated parameters
DCCpara <- DCC@model[["mpars"]]
DCCpara <- as.matrix(DCCpara[c("mu","ar1", "omega", "alpha1", "beta1"),-10])
DCCresi <- DCC@model[["residuals"]]
DCCsigma <- DCC@model[["sigma"]]
DCCab <- as.numeric(DCC@model[["mpars"]][c("dcca1", "dccb1"),10])
DCCQ <- DCC@mfit$Q[[train]]
DCCR <- DCC@mfit$R[[train]]
DCCH <- DCC@mfit$H[,,train]
DCCnu <- DCC@mfit$stdresid[train,]

#DCC bootstrap forecast for 252 days 1000 times
DCCbfr <- matrix(0,252,1000)
DCCbfv <- matrix(0,252,1000)
for (i in 1:1000){
  temp <- DCCforecast(DCCpara["omega",], DCCpara["alpha1",], DCCpara["beta1",], boot = T,
                      DCCsigma[train,], DCCab[1], DCCab[2], DCCQ, DCCR, DCCH, DCCnu, h = 252, clr)
  DCCbfr[,i] <- temp$Rp
  DCCbfv[,i] <- temp$Vp
  
}

#DCC simulate forecast for 252 days 1000 times
DCCsfr <- matrix(0,252,1000)
DCCsfv <- matrix(0,252,1000)
for (i in 1:1000){
  temp <- DCCforecast(DCCpara["omega",], DCCpara["alpha1",], DCCpara["beta1",], boot = F,
                      DCCsigma[train,], DCCab[1], DCCab[2], DCCQ, DCCR, DCCH, DCCnu, h = 252, clr)
  DCCsfr[,i] <- temp$Rp
  DCCsfv[,i] <- temp$Vp
  
}

#CCC
#get estimated parameters
CCCpara <- CCC@model[["mpars"]]
CCCpara <- as.matrix(CCCpara[c("mu","ar1", "omega", "alpha1", "beta1"),-10])
CCCresi <- CCC@model[["residuals"]]
CCCsigma <- CCC@model[["sigma"]]
CCCR <- CCC@mfit$R[[train]]
CCCH <- CCC@mfit$H[,,train]

#CCC bootstrap forecast for 252 days 1000 times
CCCbfr <- matrix(0,252,1000)
CCCbfv <- matrix(0,252,1000)
for (i in 1:1000){
  temp <- CCCforecast(CCCpara["omega",], CCCpara["alpha1",], CCCpara["beta1",], CCCsigma[train,],
                      CCCR, CCCH, h = 252, clr,  boot = T)
  CCCbfr[,i] <- temp$Rp
  CCCbfv[,i] <- temp$Vp
  
}

#CCC simulate forecast for 252 days 1000 times
CCCsfr <- matrix(0,252,1000)
CCCsfv <- matrix(0,252,1000)
for (i in 1:1000){
  temp <- CCCforecast(CCCpara["omega",], CCCpara["alpha1",], CCCpara["beta1",], CCCsigma[train,],
                      CCCR, CCCH, h = 252, clr,  boot = F)
  CCCsfr[,i] <- temp$Rp
  CCCsfv[,i] <- temp$Vp
  
}

####forecast evaluation ####
#MVRN bootstrap
MVRNb.var.5 <- eval.fcst(MVRNbfr, MVRNbfv, 1.645, 0.05, 252,1000)[[1]]
MVRNb.vvar.5 <- eval.fcst(MVRNbfr, MVRNbfv, 1.645, 0.05, 252,1000)[[2]]
MVRNb.ves.5 <- eval.fcst(MVRNbfr, MVRNbfv, 1.645, 0.05, 252,1000)[[3]]
MVRNb.es.5 <- eval.fcst(MVRNbfr, MVRNbfv, 1.645, 0.05, 252,1000)[[4]]

MVRNb.var.2 <- eval.fcst(MVRNbfr, MVRNbfv, 1.96, 0.025, 252,1000)[[1]]
MVRNb.vvar.2 <- eval.fcst(MVRNbfr, MVRNbfv, 1.96, 0.025, 252,1000)[[2]]
MVRNb.ves.2 <- eval.fcst(MVRNbfr, MVRNbfv, 1.96, 0.025, 252,1000)[[3]]
MVRNb.es.2 <- eval.fcst(MVRNbfr, MVRNbfv, 1.96, 0.025, 252,1000)[[4]]

MVRNb.var.1 <- eval.fcst(MVRNbfr, MVRNbfv, 2.326, 0.01, 252,1000)[[1]]
MVRNb.vvar.1 <- eval.fcst(MVRNbfr, MVRNbfv, 2.326, 0.01, 252,1000)[[2]]
MVRNb.ves.1 <- eval.fcst(MVRNbfr, MVRNbfv, 2.326, 0.01, 252,1000)[[3]]
MVRNb.es.1 <- eval.fcst(MVRNbfr, MVRNbfv, 2.326, 0.01, 252,1000)[[4]]

#MVRN simulation
MVRNs.var.5 <- eval.fcst(MVRNsfr, MVRNsfv, 1.645, 0.05, 252,1000)[[1]]
MVRNs.vvar.5 <- eval.fcst(MVRNsfr, MVRNsfv, 1.645, 0.05, 252,1000)[[2]]
MVRNs.ves.5 <- eval.fcst(MVRNsfr, MVRNsfv, 1.645, 0.05, 252,1000)[[3]]
MVRNs.es.5 <- eval.fcst(MVRNsfr, MVRNsfv, 1.645, 0.05, 252,1000)[[4]]

MVRNs.var.2 <- eval.fcst(MVRNsfr, MVRNsfv, 1.96, 0.025, 252,1000)[[1]]
MVRNs.vvar.2 <- eval.fcst(MVRNsfr, MVRNsfv, 1.96, 0.025, 252,1000)[[2]]
MVRNs.ves.2 <- eval.fcst(MVRNsfr, MVRNsfv, 1.96, 0.025, 252,1000)[[3]]
MVRNs.es.2 <- eval.fcst(MVRNsfr, MVRNsfv, 1.96, 0.025, 252,1000)[[4]]

MVRNs.var.1 <- eval.fcst(MVRNsfr, MVRNsfv, 2.326, 0.01, 252,1000)[[1]]
MVRNs.vvar.1 <- eval.fcst(MVRNsfr, MVRNsfv, 2.326, 0.01, 252,1000)[[2]]
MVRNs.ves.1 <- eval.fcst(MVRNsfr, MVRNsfv, 2.326, 0.01, 252,1000)[[3]]
MVRNs.es.1 <- eval.fcst(MVRNsfr, MVRNsfv, 2.326, 0.01, 252,1000)[[4]]


#MVRb bootstrap
MVRbb.var.5 <- eval.fcst(MVRbbfr, MVRbbfv, 1.645, 0.05, 252, 1000)[[1]]
MVRbb.vvar.5 <- eval.fcst(MVRbbfr, MVRbbfv, 1.645, 0.05, 252, 1000)[[2]]
MVRbb.ves.5 <- eval.fcst(MVRbbfr, MVRbbfv, 1.645, 0.05, 252, 1000)[[3]]
MVRbb.es.5 <- eval.fcst(MVRbbfr, MVRbbfv, 1.645, 0.05, 252, 1000)[[4]]

MVRbb.var.2 <- eval.fcst(MVRbbfr, MVRbbfv, 1.96, 0.025, 252, 1000)[[1]]
MVRbb.vvar.2 <- eval.fcst(MVRbbfr, MVRbbfv, 1.96, 0.025, 252, 1000)[[2]]
MVRbb.ves.2 <- eval.fcst(MVRbbfr, MVRbbfv, 1.96, 0.025, 252, 1000)[[3]]
MVRbb.es.2 <- eval.fcst(MVRbbfr, MVRbbfv, 1.96, 0.025, 252, 1000)[[4]]

MVRbb.var.1 <- eval.fcst(MVRbbfr, MVRbbfv, 2.326, 0.01, 252, 1000)[[1]]
MVRbb.vvar.1 <- eval.fcst(MVRbbfr, MVRbbfv, 2.326, 0.01, 252, 1000)[[2]]
MVRbb.ves.1 <- eval.fcst(MVRbbfr, MVRbbfv, 2.326, 0.01, 252, 1000)[[3]]
MVRbb.es.1 <- eval.fcst(MVRbbfr, MVRbbfv, 2.326, 0.01, 252, 1000)[[4]]

#MVRb simulation
MVRbs.var.5 <- eval.fcst(MVRbsfr, MVRbsfv, 1.645, 0.05, 252, 1000)[[1]]
MVRbs.vvar.5 <- eval.fcst(MVRbsfr, MVRbsfv, 1.645, 0.05, 252, 1000)[[2]]
MVRbs.ves.5 <- eval.fcst(MVRbsfr, MVRbsfv, 1.645, 0.05, 252, 1000)[[3]]
MVRbs.es.5 <- eval.fcst(MVRbsfr, MVRbsfv, 1.645, 0.05, 252, 1000)[[4]]

MVRbs.var.2 <- eval.fcst(MVRbsfr, MVRbsfv, 1.96, 0.025, 252, 1000)[[1]]
MVRbs.vvar.2 <- eval.fcst(MVRbsfr, MVRbsfv, 1.96, 0.025, 252, 1000)[[2]]
MVRbs.ves.2 <- eval.fcst(MVRbsfr, MVRbsfv, 1.96, 0.025, 252, 1000)[[3]]
MVRbs.es.2 <- eval.fcst(MVRbsfr, MVRbsfv, 1.96, 0.025, 252, 1000)[[4]]

MVRbs.var.1 <- eval.fcst(MVRbsfr, MVRbsfv, 2.326, 0.01, 252, 1000)[[1]]
MVRbs.vvar.1 <- eval.fcst(MVRbsfr, MVRbsfv, 2.326, 0.01, 252, 1000)[[2]]
MVRbs.ves.1 <- eval.fcst(MVRbsfr, MVRbsfv, 2.326, 0.01, 252, 1000)[[3]]
MVRbs.es.1 <- eval.fcst(MVRbsfr, MVRbsfv, 2.326, 0.01, 252, 1000)[[4]]


#DCC bootstrap
DCCb.var.5 <- eval.fcst(DCCbfr, DCCbfv, 1.645, 0.05, 252,1000)[[1]]
DCCb.vvar.5 <- eval.fcst(DCCbfr, DCCbfv, 1.645, 0.05, 252,1000)[[2]]
DCCb.ves.5 <- eval.fcst(DCCbfr, DCCbfv, 1.645, 0.05, 252,1000)[[3]]
DCCb.es.5 <- eval.fcst(DCCbfr, DCCbfv, 1.645, 0.05, 252,1000)[[4]]

DCCb.var.2 <- eval.fcst(DCCbfr, DCCbfv, 1.96, 0.025, 252,1000)[[1]]
DCCb.vvar.2 <- eval.fcst(DCCbfr, DCCbfv, 1.96, 0.025, 252,1000)[[2]]
DCCb.ves.2 <- eval.fcst(DCCbfr, DCCbfv, 1.96, 0.025, 252,1000)[[3]]
DCCb.es.2 <- eval.fcst(DCCbfr, DCCbfv, 1.96, 0.025, 252,1000)[[4]]

DCCb.var.1 <- eval.fcst(DCCbfr, DCCbfv, 2.326, 0.01, 252,1000)[[1]]
DCCb.vvar.1 <- eval.fcst(DCCbfr, DCCbfv, 2.326, 0.01, 252,1000)[[2]]
DCCb.ves.1 <- eval.fcst(DCCbfr, DCCbfv, 2.326, 0.01, 252,1000)[[3]]
DCCb.es.1 <- eval.fcst(DCCbfr, DCCbfv, 2.326, 0.01, 252,1000)[[4]]

#DCC simulation
DCCs.var.5 <- eval.fcst(DCCsfr, DCCsfv, 1.645, 0.05, 252,1000)[[1]]
DCCs.vvar.5 <- eval.fcst(DCCsfr, DCCsfv, 1.645, 0.05, 252,1000)[[2]]
DCCs.ves.5 <- eval.fcst(DCCsfr, DCCsfv, 1.645, 0.05, 252,1000)[[3]]
DCCs.es.5 <- eval.fcst(DCCsfr, DCCsfv, 1.645, 0.05, 252,1000)[[4]]

DCCs.var.2 <- eval.fcst(DCCsfr, DCCsfv, 1.96, 0.025, 252,1000)[[1]]
DCCs.vvar.2 <- eval.fcst(DCCsfr, DCCsfv, 1.96, 0.025, 252,1000)[[2]]
DCCs.ves.2 <- eval.fcst(DCCsfr, DCCsfv, 1.96, 0.025, 252,1000)[[3]]
DCCs.es.2 <- eval.fcst(DCCsfr, DCCsfv, 1.96, 0.025, 252,1000)[[4]]

DCCs.var.1 <- eval.fcst(DCCsfr, DCCsfv, 2.326, 0.01, 252,1000)[[1]]
DCCs.vvar.1 <- eval.fcst(DCCsfr, DCCsfv, 2.326, 0.01, 252,1000)[[2]]
DCCs.ves.1 <- eval.fcst(DCCsfr, DCCsfv, 2.326, 0.01, 252,1000)[[3]]
DCCs.es.1 <- eval.fcst(DCCsfr, DCCsfv, 2.326, 0.01, 252,1000)[[4]]

#CCC bootstrap
CCCb.var.5 <- eval.fcst(CCCbfr, CCCbfv, 1.645, 0.05, 252,1000)[[1]]
CCCb.vvar.5 <- eval.fcst(CCCbfr, CCCbfv, 1.645, 0.05, 252,1000)[[2]]
CCCb.ves.5 <- eval.fcst(CCCbfr, CCCbfv, 1.645, 0.05, 252,1000)[[3]]
CCCb.es.5 <- eval.fcst(CCCbfr, CCCbfv, 1.645, 0.05, 252,1000)[[4]]

CCCb.var.2 <- eval.fcst(CCCbfr, CCCbfv, 1.96, 0.025, 252,1000)[[1]]
CCCb.vvar.2 <- eval.fcst(CCCbfr, CCCbfv, 1.96, 0.025, 252,1000)[[2]]
CCCb.ves.2 <- eval.fcst(CCCbfr, CCCbfv, 1.96, 0.025, 252,1000)[[3]]
CCCb.es.2 <- eval.fcst(CCCbfr, CCCbfv, 1.96, 0.025, 252,1000)[[4]]

CCCb.var.1 <- eval.fcst(CCCbfr, CCCbfv, 2.326, 0.01, 252,1000)[[1]]
CCCb.vvar.1 <- eval.fcst(CCCbfr, CCCbfv, 2.326, 0.01, 252,1000)[[2]]
CCCb.ves.1 <- eval.fcst(CCCbfr, CCCbfv, 2.326, 0.01, 252,1000)[[3]]
CCCb.es.1 <- eval.fcst(CCCbfr, CCCbfv, 2.326, 0.01, 252,1000)[[4]]

#CCC simulation
CCCs.var.5 <- eval.fcst(CCCsfr, CCCsfv, 1.645, 0.05, 252,1000)[[1]]
CCCs.vvar.5 <- eval.fcst(CCCsfr, CCCsfv, 1.645, 0.05, 252,1000)[[2]]
CCCs.ves.5 <- eval.fcst(CCCsfr, CCCsfv, 1.645, 0.05, 252,1000)[[3]]
CCCs.es.5 <- eval.fcst(CCCsfr, CCCsfv, 1.645, 0.05, 252,1000)[[4]]

CCCs.var.2 <- eval.fcst(CCCsfr, CCCsfv, 1.96, 0.025, 252,1000)[[1]]
CCCs.vvar.2 <- eval.fcst(CCCsfr, CCCsfv, 1.96, 0.025, 252,1000)[[2]]
CCCs.ves.2 <- eval.fcst(CCCsfr, CCCsfv, 1.96, 0.025, 252,1000)[[3]]
CCCs.es.2 <- eval.fcst(CCCsfr, CCCsfv, 1.96, 0.025, 252,1000)[[4]]

CCCs.var.1 <- eval.fcst(CCCsfr, CCCsfv, 2.326, 0.01, 252,1000)[[1]]
CCCs.vvar.1 <- eval.fcst(CCCsfr, CCCsfv, 2.326, 0.01, 252,1000)[[2]]
CCCs.ves.1 <- eval.fcst(CCCsfr, CCCsfv, 2.326, 0.01, 252,1000)[[3]]
CCCs.es.1 <- eval.fcst(CCCsfr, CCCsfv, 2.326, 0.01, 252,1000)[[4]]

#indicator function tables
tableCCvar <- data.frame(CCCs.vvar.5,CCCs.vvar.2,CCCs.vvar.1,CCCb.vvar.5,CCCb.vvar.2, CCCb.vvar.1,
                          DCCs.var.5,DCCs.vvar.2,DCCs.vvar.1,DCCb.vvar.5,DCCb.vvar.2, DCCb.vvar.1)

tableCCes <- data.frame(CCCs.ves.5,CCCs.ves.2,CCCs.ves.1,CCCb.ves.5,CCCb.ves.2, CCCb.ves.1,
                         DCCs.ves.5,DCCs.ves.2,DCCs.ves.1,DCCb.ves.5,DCCb.ves.2, DCCb.ves.1)

tableMRvar <- data.frame(MVRNs.vvar.5,MVRNs.vvar.2,MVRNs.vvar.1,MVRNb.vvar.5,MVRNb.vvar.2, MVRNb.vvar.1,
                         MVRbs.vvar.5,MVRbs.vvar.2,MVRbs.vvar.1,MVRbb.vvar.5,MVRbb.vvar.2, MVRbb.vvar.1)
tableMRes <- data.frame(MVRNs.ves.5,MVRNs.ves.2,MVRNs.ves.1,MVRNb.ves.5,MVRNb.ves.2, MVRNb.ves.1,
                         MVRbs.ves.5,MVRbs.ves.2,MVRbs.ves.1,MVRbb.ves.5,MVRbb.ves.2, MVRbb.ves.1)

xtable::xtable(tableCCvar[c(1,2,3,4,5,7,10,15,20,30,40,50,60,70,80,90,100,125,150,175,200,225,252),])
xtable::xtable(tableCCes[c(1,2,3,4,5,7,10,15,20,30,40,50,60,70,80,90,100,125,150,175,200,225,252),])
xtable::xtable(tableMRvar[c(1,2,3,4,5,7,10,15,20,30,40,50,60,70,80,90,100,125,150,175,200,225,252),])
xtable::xtable(tableMRes[c(1,2,3,4,5,7,10,15,20,30,40,50,60,70,80,90,100,125,150,175,200,225,252),])

######### plots ########
#persistence of volatility / correlation
plot(MVRNpara$rhot[22,], col = rgb(red = 191/255, green = 0/255, blue = 69/255, alpha = 1),
     type = 'l', ylim = c(min(ydf[c(1,2,9),]),max((ydf[c(1,2,9),]))),
     xlab = 'Time', ylab = 'yt', main = 'Daily Log Realized Correlation Tech', 
     xaxt = 'n')
lines(MVRNpara$rhot[23,], col = rgb(red = 85/255, green = 161/255, blue = 0/255, alpha = 1))
lines(MVRNpara$rhot[27,], col = rgb(red = 52/255, green = 56/255, blue = 143/255, alpha = 1))
lines(MVRbpara$zetat[4,], ylim = c(0,1), col = rgb(red = 0, green = 0, blue = 0, alpha = 1))
axis(1 , at=1:(length(CRSPdat)-10), year(CRSPdat[-(1:10)]), tick = F, gap.axis = 0.63, cex.axis = 0.75)
legend(x = "topleft", legend=c('AMZN-AAPL', 'AMZN-MSFT', 'AAPL-MSFT','Tech'),
       col=c(rgb(red = 191/255, green = 0/255, blue = 69/255),
             rgb(red = 85/255, green = 161/255, blue = 0/255),
             rgb(red = 52/255, green = 56/255, blue = 143/255), "black"), lty=1, cex=0.6)

plot(ydf[22,], col = rgb(red = 191/255, green = 0/255, blue = 69/255, alpha = 1),
     type = 'l', ylim = c(min(ydf[c(22,23,27),]),max((ydf[c(22,23,27),]))),
     xlab = 'Time', ylab = 'yt', main = 'Daily Log Realized Correlation Energy', 
     xaxt = 'n')
lines(ydf[23,], col = rgb(red = 85/255, green = 161/255, blue = 0/255, alpha = 1))
lines(ydf[27,], col = rgb(red = 52/255, green = 56/255, blue = 143/255, alpha = 1))
lines(ybar[4,], ylim = c(0,1), col = rgb(red = 0, green = 0, blue = 0, alpha = 1))
axis(1 , at=1:(length(CRSPdat)-10), year(CRSPdat[-(1:10)]), tick = F, gap.axis = 0.63, cex.axis = 0.75)
legend(x = "topleft", legend=c('BP-XOM', 'BP-OXY', 'XOM-OXY','Energy'),
       col=c(rgb(red = 191/255, green = 0/255, blue = 69/255),
             rgb(red = 85/255, green = 161/255, blue = 0/255),
             rgb(red = 52/255, green = 56/255, blue = 143/255), "black"), lty=1, cex=0.6)

plot(ydf[34,], col = rgb(red = 191/255, green = 0/255, blue = 69/255, alpha = 1),
     type = 'l', ylim = c(min(ydf[c(34,35,36),]),max((ydf[c(34,35,36),]))),
     xlab = 'Time', ylab = 'yt', main = 'Daily Log Realized Correlation Retail', 
     xaxt = 'n')
lines(ydf[35,], col = rgb(red = 85/255, green = 161/255, blue = 0/255, alpha = 1))
lines(ydf[36,], col = rgb(red = 52/255, green = 56/255, blue = 143/255, alpha = 1))
lines(ybar[6,], ylim = c(0,1), col = rgb(red = 0, green = 0, blue = 0, alpha = 1))
axis(1 , at=1:(length(CRSPdat)-10), year(CRSPdat[-(1:10)]), tick = F, gap.axis = 0.63, cex.axis = 0.75)
legend(x = "topleft", legend=c('TGT-WMT', 'TGT-BBY', 'WMT-BBY','Retail'),
       col=c(rgb(red = 191/255, green = 0/255, blue = 69/255),
             rgb(red = 85/255, green = 161/255, blue = 0/255),
             rgb(red = 52/255, green = 56/255, blue = 143/255), "black"), lty=1, cex=0.6)

plot(ydf[1,], col = rgb(red = 191/255, green = 0/255, blue = 69/255, alpha = 1),
     type = 'l', ylim = c(min(ydf[c(1,4,6),]),max((ydf[c(1,4,6),]))),
     xlab = 'Time', ylab = 'yt', main = 'Daily Log Realized Correlation Intra Sector', 
     xaxt = 'n')
lines(ydf[4,], col = rgb(red = 85/255, green = 161/255, blue = 0/255, alpha = 1))
lines(ydf[6,], col = rgb(red = 52/255, green = 56/255, blue = 143/255, alpha = 1))
lines(colMeans(ybar[c(1,4,6),]), ylim = c(0,1), col = rgb(red = 0, green = 0, blue = 0, alpha = 1))
axis(1 , at=1:(length(CRSPdat)-10), year(CRSPdat[-(1:10)]), tick = F, gap.axis = 0.63, cex.axis = 0.75)
legend(x = "topleft", legend=c('Tech', 'Energy', 'Retail','Average Intra Sector'),
       col=c(rgb(red = 191/255, green = 0/255, blue = 69/255),
             rgb(red = 85/255, green = 161/255, blue = 0/255),
             rgb(red = 52/255, green = 56/255, blue = 143/255), "black"), lty=1, cex=0.6)

plot(ydf[2,], col = rgb(red = 191/255, green = 0/255, blue = 69/255, alpha = 1),
     type = 'l', ylim = c(min(ydf[c(2,3,5),]),max((ydf[c(2,3,5),]))),
     xlab = 'Time', ylab = 'yt', main = 'Daily Log Realized Correlation Inter Sector', 
     xaxt = 'n')
lines(ydf[3,], col = rgb(red = 85/255, green = 161/255, blue = 0/255, alpha = 1))
lines(ydf[5,], col = rgb(red = 52/255, green = 56/255, blue = 143/255, alpha = 1))
lines(colMeans(ybar[c(2,3,5),]), ylim = c(0,1), col = rgb(red = 0, green = 0, blue = 0, alpha = 1))
axis(1 , at=1:(length(CRSPdat)-10), year(CRSPdat[-(1:10)]), tick = F, gap.axis = 0.63, cex.axis = 0.75)
legend(x = "topleft", legend=c('Tech-Energy', 'Tech-Retail', 'Energy-Retail','Average Inter Sector'),
       col=c(rgb(red = 191/255, green = 0/255, blue = 69/255),
             rgb(red = 85/255, green = 161/255, blue = 0/255),
             rgb(red = 52/255, green = 56/255, blue = 143/255), "black"), lty=1, cex=0.6)


#per model 5%, 2.5%, 1% ES in stock plot
plot(equiport[c(train:(train+252))],type='l', main = 'Bootstrap Forecast ES MVR',
     ylab = "Return", xlab = "Time t+k", xaxt = 'n',
     ylim = c(min(equiport[c(train:(train+252))], MVRNb.es.5),max(equiport[c(train:(train+252))])) )
lines(MVRNb.es.5, col = rgb(red = 191/255, green = 0/255, blue = 69/255))
lines(MVRNb.es.2, col = rgb(red = 85/255, green = 161/255, blue = 0/255))
lines(MVRNb.es.1, col = rgb(red = 52/255, green = 56/255, blue = 143/255))
legend(x = "topleft", legend=c("5%", "2.5%", "1%"),
       col=c(rgb(red = 191/255, green = 0/255, blue = 69/255),
             rgb(red = 85/255, green = 161/255, blue = 0/255),
             rgb(red = 52/255, green = 56/255, blue = 143/255)), lty=1, cex=0.6)
axis(1 , at=1:252, paste(month(CRSPdat[train:(train+251)]),year(CRSPdat[train:(train+251)]), sep = '.'), 
     tick = F, cex.axis = 0.75)

#per model 5%, 2.5%, 1% VaR
plot(equiport[c(train:(train+252))],type='l', main = 'Bootstrap Forecast VaR MVR',
     ylab = "Return", xlab = "Time t+k", xaxt = 'n',
     ylim = c(min(equiport[c(train:(train+252))],MVRNb.var.5),max(equiport[c(train:(train+252))])))
lines(CCCs.var.5, col = rgb(red = 191/255, green = 0/255, blue = 69/255))
lines(CCCs.var.2, col = rgb(red = 85/255, green = 161/255, blue = 0/255))
lines(CCCs.var.1, col = rgb(red = 52/255, green = 56/255, blue = 143/255))
legend(x = "topleft", legend=c("5%", "2.5%", "1%"),
       col=c(rgb(red = 191/255, green = 0/255, blue = 69/255),
             rgb(red = 85/255, green = 161/255, blue = 0/255),
             rgb(red = 52/255, green = 56/255, blue = 143/255)), lty=1, cex=0.6)
axis(1 , at=1:252, paste(month(CRSPdat[train:(train+251)]),year(CRSPdat[train:(train+251)]), sep = '.'), 
     tick = F, cex.axis = 0.75)

#graphs comparing models ES violations
plot(CCCb.ves.1, col = rgb(red = 85/255, green = 161/255, blue = 0/255),
     ylim = c(-0.03,0.3), xlab = 'Time t+k', ylab = 'Indicator function',
     main = 'Indicator function for ES 1%')
points(DCCs.ves.1, col = rgb(red = 191/255, green = 0/255, blue = 69/255))
points(MVRNb.ves.1, col = rgb(red = 254/255, green = 158/255, blue = 0/25585))
points(MVRbb.ves.1, col = rgb(red = 52/255, green = 56/255, blue = 143/255))
abline(h=0)
legend(x = "topright", legend=c("CCC", "DCC", "MVR", "MVRB"),
       col=c(rgb(red = 85/255, green = 161/255, blue = 0/255),
             rgb(red = 191/255, green = 0/255, blue = 69/255),
             rgb(red = 254/255, green = 158/255, blue = 0/255),
             rgb(red = 52/255, green = 56/255, blue = 143/255)), lty=1, cex=0.6)

#graphs comparing models VaR violations
plot(CCCb.vvar.1, col = rgb(red = 85/255, green = 161/255, blue = 0/255),
     ylim = c(-0.04,0.16), xlab = 'Time t+k', ylab = 'Indicator function',
     main = 'Indicator function for VaR 1%')
points(DCCb.vvar.1, col = rgb(red = 191/255, green = 0/255, blue = 69/255))
points(MVRNb.vvar.1, col = rgb(red = 254/255, green = 158/255, blue = 0/255))
points(MVRbb.vvar.1, col = rgb(red = 52/255, green = 56/255, blue = 143/255))
abline(h=0)
legend(x = "topright", legend=c("CCC", "DCC", "MVR", "MVRB"),
       col=c(rgb(red = 85/255, green = 161/255, blue = 0/255),
             rgb(red = 191/255, green = 0/255, blue = 69/255),
             rgb(red = 254/255, green = 158/255, blue = 0/255),
             rgb(red = 52/255, green = 56/255, blue = 143/255)), lty=1, cex=0.6)


#sigma distance for equiport forecast window
plot(equiprob[train:(train+252)],type='l', main = 'Return Sigma Distance',
     ylab = "Sigma", xlab = "Time t+k", xaxt = 'n')
abline(h = -1.645, col = rgb(red = 191/255, green = 0/255, blue = 69/255))
abline(h = -1.95, col = rgb(red = 85/255, green = 161/255, blue = 0/255))
abline(h = -2.364, col = rgb(red = 52/255, green = 56/255, blue = 143/255))

legend(x = "topleft", legend=c("5%", "2.5%", "1%"),
       col=c(rgb(red = 191/255, green = 0/255, blue = 69/255),
             rgb(red = 85/255, green = 161/255, blue = 0/255),
             rgb(red = 52/255, green = 56/255, blue = 143/255)), lty=1, cex=0.6)
axis(1 , at=1:252, paste(month(CRSPdat[train:(train+251)]),year(CRSPdat[train:(train+251)]), sep = '.'), 
     tick = F, cex.axis = 0.75)


