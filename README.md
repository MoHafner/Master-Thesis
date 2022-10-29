# Master-Thesis
Forecasts of Risk Measurements using the Multivariate Realized GARCH Model
The highfrequency data was downloaded from the TAQ data base via the Wharton cloud. The code can be found in the file MA.R.
The original realized correlation and covariance as the intraday price data are in the files: corrmatfin.csv and covmatfin.csv, respectively. 
The realized correaltion and covariance were log vectorized and subse- quentially saved as: ydf and xdf. These were used in the model estimation.
The daily close-to-close return data was downloaded from CRSP data base savedin the CRSP.csv file. 
The estimation was done in python with the code in the file ”MA.py”.
The indicator function and the plots were done in R with the code in the file ”MA.R”.
