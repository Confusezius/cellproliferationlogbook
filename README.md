## Logbook for Cellproliferation studies
This repo contains an older project implementing a logbook for cellproliferation studies (in german):

* One can add proliferation points for different cell cultures, which are then stored and evaluated. Through various regression models (variants on logistic regression) the programm determines whether proliferation points reveal a healthy or dying cell culture.

* This is implemented fully low-end by hand, i.e. optimisation via Simplex/Nelder-Mead in plain javascript.
![NM](/IMAGES/optimone.png)

* Summaries/Data can be send and shared as Google Plots and tables via email.

* The full css, html and js is placed within the folder `FRONTEND`, which needs to be downloaded completely.

__NOTE__: Only the frontend is found in this repository. It is sufficient if one wishes to work locally and not having data stored in a database. Additionally, this project uses older versions of _JQuery_ and _Bootstrap_ and is therefore long obsolete.

## Impressions
The following image provides a flowchart over the program setup:
![Setup](/IMAGES/Cellregulator_flow.png)
