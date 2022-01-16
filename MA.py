# -*- coding: utf-8 -*-
"""
###########################################################
#Author: Moritz Hafner 16-609-778                       ###  
#Context: script to do the Maximum Likelihood           ###
          estimation of the MVR GARCH and the           ###
          MVR Block GARCH                               ###
#Master's Thesis in MiQEF                               ###
###########################################################

"""
import pandas as pd
import os as os
import numpy as np
import scipy as sp
from scipy.linalg import expm
from scipy.optimize import minimize

def logmat(C):
    """
    Parameters
    ----------
    C : input matrix
    Returns log of matrix
    -------
    """
    eav = np.linalg.eig(C)[0]
    evec = np.linalg.eig(C)[1]
    leav = np.log(eav)
    dleav = np.diag(leav)
    lmat = evec@dleav@np.transpose(evec)
    return lmat
    
    
def logmatinv(v, tol_value):
    """
    v = lower tri
    tol_value = tolerance = 1e-8
    """
    n = (0.5*(1+np.sqrt(1+8*len(v)))).astype(int)
    iter_number = -1
    G = np.zeros((n,n))
    G[np.tril_indices(n,-1)] = v
    G = G+np.transpose(G)
    diag_vec = np.repeat(1,9)
    conv = max(np.sqrt(n), np.sqrt(n)*tol_value)
    while (conv > np.sqrt(n)*tol_value) :
      diag_delta = np.log(np.diag(expm(G)))
      diag_vec = diag_vec - diag_delta
      np.fill_diagonal(G, diag_vec)
      conv = np.linalg.norm(diag_delta)
      iter_number = iter_number + 1
      C = sp.linalg.expm(G)
    
    return C

def qll(theta, r, x, y, rho, h, N):
    """
    theta : paramteres
    r : daily return
    x : daily realized covariance
    y : daily realized correlation
    rho :starting value for rho
    h : starting value for h
    N : days used for optimization
    
    returns log likelihood
    """
    #unknown parameters
    omega = theta[range(0,9)]
    beta = np.diag(theta[range(9,18)])
    tau1 = np.diag(theta[range(18,27)])
    tau2 = np.diag(theta[range(27,36)])
    gamma = np.diag(theta[range(36,45)])
    omegatilde = theta[range(45,81)]
    betatilde = np.diag(theta[range(81,117)])
    gammatilde = np.diag(theta[range(117,153)])  
    xi = theta[range(153,162)]
    phi = np.diag(theta[range(162,171)])
    delta1 = np.diag(theta[range(171,180)])
    delta2 = np.diag(theta[range(180,189)])
    xitilde = theta[range(189,225)]
    phitilde = np.diag(theta[range(225,261)])
    
    #help variables
    mu = np.transpose(rdf).mean()
    I = np.ones(9)
    
    #initialize arrays
    lht = np.zeros((9,2))
    zt = np.zeros((9,2))
    rhot = np.zeros((36,2))
    Ct = np.zeros((9,9))
    nu = np.zeros(9)
    nutilde = np.zeros(36)
    u = np.zeros(45)
    log_lika = np.zeros(N)
    log_likb = np.zeros((N,45,45))
    
    #initialize parameters
    lht[:,0] = np.log(h)
    rt = r[:,[0,1]]
    zt[:,0] = (r[:,0]-mu)*np.exp(lht[:,0])**(-0.5)
    rhot[:,0] = rho
    Ct = logmatinv(rhot[:,0], 1e-15)
    xt = x[:,[0,1]]
    yt = y[:,[0,1]]
    nu = np.log(xt[:,0]) - xi - phi@lht[:,0]-(delta1@zt[:,0]+delta2@(zt[:,0]*zt[:,0]-I))
    nutilde = yt[:,0] - xitilde - phitilde@rhot[:,0]
    u = np.concatenate((nu,nutilde), axis = 0)
    log_lika[0] = np.sum(lht[:,0], axis = 0)+np.log(np.linalg.det(Ct))+zt[:,0]@np.linalg.inv(Ct)@(zt[:,0])
    log_likb[0,:,:] = u@np.transpose(u)
    
    #
    for i in range(1,N):
        #update variables
        rt[:,1] = r[:,i]; xt[:,1] = x[:,i]; yt[:,1] = y[:,i];
        #GARCH equations h,rho,C
        lht[:,1] =  omega + beta@lht[:,0] + tau1@zt[:,0]+tau2@(zt[:,0]*zt[:,0]-I) + gamma@np.log(xt[:,0])
        rhot[:,1] = omegatilde + betatilde@rhot[:,0] + gammatilde@yt[:,0]
        Ct = logmatinv(rhot[:,1], 1e-15)
        #measurment equations z,u
        zt[:,1] = (rt[:,1]-mu)*(np.exp(lht[:,1]))**(-0.5)
        nu = np.log(xt[:,1]) - xi - phi@lht[:,1] - (delta1@zt[:,1] + delta2@(zt[:,1]*zt[:,1]-I))
        nutilde = yt[:,1] - xitilde - phitilde@rhot[:,1]
        u = np.concatenate((nu,nutilde), axis = 0)[np.newaxis]
        #loglikelihood equation 10 (Archakov, Hansen and Lunde, 2020)
        log_lika[i] = np.sum(lht[:,1], axis = 0) + np.log(np.linalg.det(Ct)) + zt[:,1]@np.linalg.inv(Ct)@zt[:,1]
        log_likb[i,:,:] = u.T@u
        #update variables
        lht[:,0] = lht[:,1]; zt[:,0] = zt[:,1]; rhot[:,0] = rhot[:,1]; 
        rt[:,0] = rt[:,1]; xt[:,0] = xt[:,1]; yt[:,0] = yt[:,1];
        
    sum_lika = -0.5*np.sum(log_lika, axis = 0)
    sum_likb = 0.5*N*np.log(np.linalg.det(log_likb.mean(axis=0)))
    sum_lik = sum_lika-sum_likb
    #print(omega); print(beta); print(gamma); print(tau1); print(tau2); print(omegatilde);
    #print(betatilde); print(gammatilde); print(xi); print(phi); print(delta1);
    #print(delta2); print(xitilde); print(phitilde)
    print((sum_lika, sum_likb, -sum_lik))
    print(theta)
    return -sum_lik


def block1(x):
    """
    x = vector
    """
    x[[0,1,2]] = np.mean(x[[0,1,2]])
    x[[3,4,5]] = np.mean(x[[3,4,5]])
    x[[6,7,8]] = np.mean(x[[6,7,8]])
    
    return x


def block2(x):
    """
    x = vector with correlations lower tri
    """
    x[[0,1,8]] = np.mean(x[[0,1,8]])
    x[[2,3,4,9,10,11,15,16,17]] = np.mean(x[[2,3,4,9,10,11,15,16,17]])
    x[[5,6,7,12,13,14,18,19,20]] = np.mean(x[[5,6,7,12,13,14,18,19,20]])
    x[[21,22,26]] = np.mean(x[[21,22,26]])
    x[[23,24,25,27,28,29,30,31,32]] = np.mean(x[[23,24,25,27,28,29,30,31,32]])
    x[[33,34,35]] = np.mean(x[[33,34,35]])
    
    return x


def qll_bl(theta, r, x, y, zeta, h, N):
    """
    theta : paramteres
    r : daily return
    x : daily realized covariance
    y : daily realized correlation
    rho :starting value for rho
    h : starting value for h
    N : days used for optimization
    
    returns log likelihood
    """
    #unknown parameters
    omega = theta[range(0,9)]
    beta = np.diag(theta[range(9,18)])
    tau1 = np.diag(theta[range(18,27)])
    tau2 = np.diag(theta[range(27,36)])
    gamma = np.diag(theta[range(36,45)])
    omegabar = theta[range(45,51)]
    betabar = np.diag(theta[range(51,57)])
    gammabar = np.diag(theta[range(57,63)])  
    xi = theta[range(63,72)]
    phi = np.diag(theta[range(72,81)])
    delta1 = np.diag(theta[range(81,90)])
    delta2 = np.diag(theta[range(90,99)])
    xibar = theta[range(99,105)]
    phibar = np.diag(theta[range(105,111)])
    
    #help variables
    mu = np.transpose(rdf).mean()
    I = np.ones(9)
    
    #initialize arrays
    lht = np.zeros((9,2))
    zt = np.zeros((9,2))
    zetat = np.zeros((6,2))
    Ct = np.zeros((9,9))
    nu = np.zeros(9)
    nubar = np.zeros(36)
    u = np.zeros(15)
    log_lika = np.zeros(N)
    log_likb = np.zeros((N,15,15))
    
    #initialize parameters
    lht[:,0] = np.log(h)
    rt = r[:,[0,1]]
    zt[:,0] = (r[:,0]-mu)*np.exp(lht[:,0])**(-0.5)
    zetat[:,0] = zeta
    Ct = logmatinv(A@zetat[:,0], 1e-15)
    xt = x[:,[0,1]]
    yt = y[:,[0,1]]
    nu = np.log(xt[:,0]) - xi - phi@lht[:,0]-(delta1@zt[:,0]+delta2@(zt[:,0]*zt[:,0]-I))
    nubar = yt[:,0] - xibar- phibar@zetat[:,0]
    u = np.concatenate((nu,nubar), axis = 0)
    log_lika[0] = np.sum(lht[:,0], axis = 0)+np.log(np.linalg.det(Ct))+zt[:,0]@np.linalg.inv(Ct)@(zt[:,0])
    log_likb[0,:,:] = u@np.transpose(u)
    
    #
    for i in range(1,N):
        #update variables
        rt[:,1] = r[:,i]; xt[:,1] = x[:,i]; yt[:,1] = y[:,i];
        #GARCH equations h,rho,C
        lht[:,1] =  omega + beta@lht[:,0] + tau1@zt[:,0]+tau2@(zt[:,0]*zt[:,0]-I) + gamma@np.log(xt[:,0])
        zetat[:,1] = omegabar + betabar@zetat[:,0] + gammabar@yt[:,0]
        Ct = logmatinv(A@zetat[:,1], 1e-15)
        #measurment equations z,u
        zt[:,1] = (rt[:,1]-mu)*(np.exp(lht[:,1]))**(-0.5)
        nu= np.log(xt[:,1]) - xi - phi@lht[:,1] - (delta1@zt[:,1] + delta2@(zt[:,1]*zt[:,1]-I))
        nubar = yt[:,1] - xibar - phibar@zetat[:,1]
        u = np.concatenate((nu,nubar), axis = 0)[np.newaxis]
        #loglikelihood equation 10 (Archakov, Hansen and Lunde, 2020)
        log_lika[i] = np.sum(lht[:,1], axis = 0) + np.log(np.linalg.det(Ct)) + zt[:,1]@np.linalg.inv(Ct)@zt[:,1]
        log_likb[i,:,:] = u.T@u
        #update variables
        lht[:,0] = lht[:,1]; zt[:,0] = zt[:,1]; zetat[:,0] = zetat[:,1]; 
        rt[:,0] = rt[:,1]; xt[:,0] = xt[:,1]; yt[:,0] = yt[:,1];
        
    sum_lika = -0.5*np.sum(log_lika, axis = 0)
    sum_likb = 0.5*N*np.log(np.linalg.det(log_likb.mean(axis=0)))
    sum_lik = sum_lika-sum_likb
    #print(omega); print(beta); print(gamma); print(tau1); print(tau2); print(omegatilde);
    #print(betatilde); print(gammatilde); print(xi); print(phi); print(delta1);
    #print(delta2); print(xitilde); print(phitilde)
    print((sum_lika, sum_likb, -sum_lik))
    print(theta)
    return -sum_lik

    
########## read data
os.chdir("/Users/Moritz/Documents/MA/")

ydf = pd.read_csv("estimation_data/ydf.csv")
ydf = ydf.drop("Unnamed: 0", axis = 1)
ydf = np.transpose(ydf)
ydf = np.array(ydf)

xdf = pd.read_csv("estimation_data/xdf.csv")
xdf = xdf.drop("Unnamed: 0", axis = 1)
xdf = np.transpose(xdf)
xdf = np.array(xdf)

rdf = pd.read_csv("estimation_data/clr.csv")
rdf = rdf.rename(rdf.iloc[:,0])
rdf = rdf.drop("Unnamed: 0", axis = 1)


h = np.cov(rdf)
h = np.diag(h)

C = np.transpose(rdf).corr()
logC = logmat(C)
rho = np.array(logC[np.tril_indices_from(logC, k=-1)]) #get lowert tri without diag
Cr = logmatinv(rho, 1e-8)

rdf = np.array(rdf)

train = round(0.8*4268)

### estimation of Multivaraite Realized GARCH
init = np.concatenate((np.repeat(0.1,9), np.repeat(0.7,9),np.repeat(0,9), np.repeat(0,9), np.repeat(0.3,9),
                           np.repeat(0,36), np.repeat(0.9,36),np.repeat(0.09,36), 
                           np.repeat(-0.2,9),np.repeat(0.1,9),np.repeat(0,9), np.repeat(0.05,9),
                           np.repeat(0,36),np.repeat(1,36)), axis = 0)

mle_bfgs = minimize(fun = qll, x0 = init, args = (rdf,xdf,ydf,rho,h, train),
                    method = 'BFGS')

### estimation of Multivaraite Realized GARCH with block correlation
A = np.zeros((36, 6))
A[[0,1,8],0] = 1
A[[2,3,4,9,10,11,15,16,17],1] = 1
A[[5,6,7,12,13,14,18,19,20],2] = 1
A[[21,22,26],3] = 1
A[[23,24,25],4] = 1
A[range(27,33),4] = 1
A[[33,34,35],5] = 1


yblock = ydf
for i in range(len(ydf.transpose())):
    yblock[:,i] = block2(ydf[:,i])

ybar = np.zeros((6,len(yblock.transpose())))

for i in range(len(ybar.transpose())):
    ybar[:,i] = pd.unique(yblock[:,i])

zeta = block2(rho)
zeta = pd.unique(zeta)

init = np.concatenate((np.repeat(0.1,9), np.repeat(0.7,9),np.repeat(0,9), np.repeat(0,9), np.repeat(0.25,9),
                           np.repeat(0,6), np.repeat(0.75,6),np.repeat(0.2,6), 
                           np.repeat(-0.2,9),np.repeat(0.1,9),np.repeat(0,9), np.repeat(0.05,9),
                           np.repeat(0,6),np.repeat(1,6)), axis = 0)

mle_bfgs_bl = minimize(fun = qll_bl, x0 = init, args = (rdf,xdf,ybar,zeta,h,train),
                    method = 'BFGS')



