// Calculations Javascript

//penalty_logistic2 calculates the logistic penalty function for two parameters
function penalty_logistic2(A, t, M){
	r = A[0];
	t0= A[1];
	var h=numeric.pow(numeric.add(1,numeric.exp(numeric.mul(-1*r,numeric.sub(t,t0)))),-1);
	var numerator   =numeric.dotVV(h,M);
	numerator=-1*numerator*numerator;
	var denominator =numeric.dotVV(h,h);
	return numerator/denominator;
	/*var z =0;
	for(var i=0;i<h.length;i++){
		z = z+Math.sqrt(Math.pow((M[i]-h[i]),2));
	}
	return z;	*/
	
}

//penalty_logistic3 calculates the logistic penalty function for four parameters
function penalty_logistic3(A,t,M){
	var K = A[0];
	var r = A[1];
	var t0= A[2];
	var ad= A[3];	
	var h=numeric.add(numeric.mul(numeric.pow(numeric.add(1,numeric.exp(numeric.mul(-1*r,numeric.sub(t,t0)))),-1),K),ad);
	var z = 0;
	for(var i=0;i<h.length;i++){
		z = z+(Math.pow((M[i]-h[i])/h[i],2));
	}
	return z;	
}

// logistic_func() calculates the logistic function without the addition variable ad
function logistic_func2(t,K,r,t0){
	return numeric.div(K,numeric.add(1,numeric.exp(numeric.mul(-1*r,numeric.sub(t,t0)))));
}

// logistic_func() calculates the logistic function with the addition variable ad
function logistic_func(t,K,r,t0,ad){
	return numeric.add(numeric.div(K,numeric.add(1,numeric.exp(numeric.mul(-1*r,numeric.sub(t,t0))))),ad);
}

function sum2(A){
	var s = 0;
	for(var i=0;i<A.length;i++){
		s = s+Math.pow(A[i],2);
	}
	return s;
}

function sum(A){
	var s = 0;
	for(var i=0;i<A.length;i++){
		s = s+A[i];
	}
	return s;
}
// getcolumn() returns the specified column with the given index from a 2d-array
function getcolumn(B,index,leng){
	var endarr=[];
	for(var i=0;i<leng;i++){
		endarr.push(B[i][index]);
	}
	return endarr;
	
}

// getrow() returns the specified row with the given index from a 2d-array
function getrow(B,index,leng){
	var endarr=[];
	for(var i=0;i<leng;i++){
		endarr.push(B[index][i]);
	}
	return endarr;
	
}

// delcol() deletes a column with index [index] from 2d-array B
function delcol(B,index,leng1,leng2){
	var endarr=[];
	for(var i =0;i<leng1;i++){
		endarr[i]=new Array(leng2-1);
	}
	var collect = 0;
	for(var i =0;i<leng2;i++){
		if(i!=index){
			for(var j=0;j<leng1;j++){
				endarr[j][collect]=B[j][i];
			}	
		collect=collect+1	
		}
	}
	return endarr;
}

// delrow() deletes a row with index [index] from 2d-array B
/*function delrow(B,index,leng1,leng2){
	var endarr=[];
	for(var i =0;i<leng1;i++){
		endarr[i]=new Array(leng2-1);
	}
	var collect = 0;
	for(var i =0;i<leng1;i++){
		if(i!=index){
			for(var j=0;j<leng2;j++){
				endarr[collect][j]=B[i][j]);
			}		
		collect=collect+1;
		}
	}
	return endarr;
}*/

//fnminimizer finds the local minimium from any arbitrary, smooth or non-smooth function using 
//a Downhill-Simplex algorithm (to a precision of epsilon).
function fnminimizer(Fn,paramguess,t,M,epsilon){
	var param=paramguess.length;
	var precision=100;
	var V = new Array(param);
	var bestv_collect = new Array(param);
	var checksum = sum2(M);
	
	for(var i=0;i<param;i++){
		V[i]=new Array(param+1);
	}
	
	for(var i=0;i<param;i++){
		V[i][0]=paramguess[i];
	}

	for(var j=1;j<param+1;j++){
		for(var i=0;i<param;i++){
			V[i][j]=paramguess[i]+0.05*paramguess[i]*(Math.random()*3);
		}
	}
	fnvals=new Array(param+1);
	for(var i=0;i<fnvals.length;i++){
		G = getcolumn(V,i,param);	
		fnvals[i]=Fn(G, t, M);
	}
	var counter=0;
	var pcoll=new Array();	

	while(precision>epsilon){
		var maxdex=fnvals[0];
		var index=0;
		for(var i=1;i<fnvals.length;i++){
			if(fnvals[i]>maxdex){
				maxdex=fnvals[i];
				index=i;
			}
		}
		
		var mindex=fnvals[0];
		var index2=0;
		for(var i=1;i<fnvals.length;i++){
			if(fnvals[i]<mindex){
				mindex=fnvals[i];
				index2=i;
			}
		}
				
		fnnew=fnvals;
		fnnew.splice(index,1);		
		var V_new=delcol(V,index,param,param+1);
		var V_temp=getcolumn(V,index,param);
		var a = [];
		for(var i=0;i<param;i++){
			temp=0;
			for(var j=0;j<param;j++){
				temp=temp+V_new[i][j];
			}
			a.push(temp);
		}
		var refl_x = numeric.div(a,(param));

		var new_p = [];
		
		for(var i=0;i<param;i++){
			new_p.push(2*refl_x[i]-V[i][index]);
		}
		var fn_ref=Fn(new_p,t,M);
		
		sumnum=0;
		for(var i=0;i<param;i++){
			if(fn_ref>=fnnew[i]){
				sumnum=sumnum+1;
			}
		}
		if(sumnum==1){	
			V=V_new.slice();
			for(var i=0;i<param;i++){
				V[i].push(new_p[i]);
			}
		}else if(sumnum==0){	
			new_p2=[];
			for(var i=0;i<param;i++){
				new_p2.push(refl_x[i]+2*(refl_x[i]-V[i][index]));
			}
			if(Fn(new_p2,t,M)<Fn(new_p,t,M)){
				V=V_new.slice();
				for(var i=0;i<param;i++){
					V[i].push(new_p2[i]);
				}				
			}else{
				V=V_new.slice();
				for(var i=0;i<param;i++){
					V[i].push(new_p[i]);
				}				
			}
			
		}else if(sumnum>1){
			new_p=[];
			for(var i=0;i<param;i++){
				new_p.push(refl_x[i]-0.5*(refl_x[i]-V[i][index]));			
			}
		}	

		fn_ref2=Fn(new_p,t,M);
		sumnum=0;
		for(var i=0;i<param;i++){
			if(fn_ref2[i]>=fnnew[i]){
				sumnum=sumnum+1;
			}
		}		
		if(sumnum<=1){
			V=V_new.slice();		
			for(var i=0;i<param;i++){
				V[i].push(new_p[i]);
			}
		}else if(sumnum>1){
			V_best=[];
			for(var i=0;i<param;i++){
				V_best.push(V[i][index2]);
			}
			V_bad=V.slice();
			for(var i=0;i<param;i++){
				V_bad[i].splice(index2,1);
			}
			V_rep=new Array(param);
			for(var i=0;i<param;i++){
				V_rep[i]=new Array(param);
			}
			for(var i=0;i<param;i++){
				for(var j=0;j<param;j++){
					V_rep[i][j]=V_best[i]+0.5*(V_bad[i][j]-V_best[i]);
				}
			}
			V = V_rep.slice();
			for(var i=0;i<param;i++){
				V[i].push(V_best[i]);
			}					
		}
		for(var i=0;i<param+1;i++){
			var G = getcolumn(V,i,param);
			fnvals[i]=Fn(G,t,M);
		}
		var check=new Array(param+1);
		for(var i=0;i<param+1;i++){
			check[i]=new Array(param+1);
		}
		
		for(var i=0;i<param+1;i++){
			for(var j=0;j<param+1;j++){
				check[i][j]=Math.pow(fnvals[i]-fnvals[j],2);
			}
		}
		var trilsum=0;
		for(var i=0;i<param+1;i++){
			for(var j=0;j<i+1;j++){
				trilsum=check[i][j]+trilsum;
			}
		}
		precision = trilsum/(param+1);
		if(counter>=2000){
			break;
		}
		counter=counter+1
		//if(counter%2==0){
		//	alert("Precision: "+precision+", Counter: "+counter+"\n"+"fnvals: "+fnvals);
		//}
	}
	var bestv = [];
	for(var i=0;i<param;i++){
		var tempsum=0;
		for(var j=0;j<param+1;j++){
			tempsum=tempsum+V[i][j];
		}
		bestv.push(tempsum/(param+1));
	}
	return bestv;
}

//prolcontrol() is the main executable function, which calls all the other functions.
function prolcontrol(data,paramguess,epsilon,g,extradx,extrady,extraname,extrax,extray,check1,check2){
	var divinx = 1;
	var diviny = 1;	
	var pname = "Figure";
	var xname = "x-Axis";	
	var yname = "y-Axis";		
	if((extradx!==undefined)&&(extradx!=="")&&(extradx!==NaN)){divinx=parseFloat(extradx)};
	if((extrady!==undefined)&&(extrady!=="")&&(extrady!==NaN)){diviny=parseFloat(extrady)};
	if((extraname!==undefined)&&(extraname!=="")&&(extraname!==NaN)){pname=extraname; alert(pname);};
	if((extrax!==undefined)&&(extrax!=="")&&(extrax!==NaN)){xname=extrax};
	if((extray!==undefined)&&(extray!=="")&&(extray!==NaN)){yname=extray};			
	$("#block").show();
	$("#progressb").fadeIn('fast');
	B = data.split(",");
	B1 = [];
	B2 = [];
	for (var i=0;i<B.length;i++){
		if(i%2==0){
			B1.push(Number(B[i]));
		}else{
			B2.push(Number(B[i]));			
		}
	}
	document.getElementById("progressbb").style.width='10%';    
	var t = [];
	var M = [];
	//for(var i=0;i<(B.length/2);i++){
	//	t.push(B2[(B.length/2)-1-i]);
	//	M.push(B1[(B.length/2)-1-i]);		
	//}	
	if(check2==true && check1==true){
		for(var i=0;i<(B.length/2);i++){
			t.push(B2[(B.length/2-1)-i]/divinx);
			M.push(B1[(B.length/2-1)-i]/diviny);		
		}
	}else if(check2==true && check1==false){
		for(var i=0;i<(B.length/2);i++){
			t.push(B2[i]/divinx);
			M.push(B1[i]/diviny);	
		}
	}else if(check2==false && check1==true){
		for(var i=0;i<(B.length/2);i++){
			t.push(B1[(B.length/2-1)-i]/divinx);
			M.push(B2[(B.length/2-1)-i]/diviny);	
		}		
	}else{
		for(var i=0;i<(B.length/2);i++){
			t.push(B1[i]/divinx);
			M.push(B2[i]/diviny);
		}		
	}
	//Algorithm start	
	var tt = numeric.linspace(t[0],t[t.length-1],6000);
	var num_r = 100;
	var rvec=new Array(num_r);
	rvec[0]=0.0000001;
	
	for(var i=1;i<num_r;i++){
		rvec[i]=rvec[i-1]*1.2303;
	}
	document.getElementById("progressbb").style.width='20%';	
	var num_t0=300;
	t0_vec=numeric.linspace(t[0],t[t.length-1],num_t0);
	penalty_array=new Array(num_t0);
	for(var i = 0;i<num_t0;i++){
		penalty_array[i]=new Array(num_r);
	}
	var comp=[];
	var inputt = [];
	for(var i=0;i<num_t0;i++){
		for(var j=0;j<num_r;j++){
			inputt[0]=rvec[j];
			inputt[1]=t0_vec[i];		
			penalty_array[i][j]=penalty_logistic2(inputt, t, M);
		}
	}
	var min=[];
	var idx=[];
	for (var i=0;i<num_r;i++){
		var minval=penalty_array[0][i];
		var idxval=0;
		for(var j=1;j<num_t0;j++){
			if(penalty_array[j][i]<minval){
				minval=penalty_array[j][i];
				idxval=j;
			}		
		}
		min.push(minval);
		idx.push(idxval);
	}
	var ming =min[0];	
	for(var i=0;i<min.length;i++){
		if(min[i]<ming){
			minidx2=i;
			ming=min[i];
		}
	}
	document.getElementById("progressbb").style.width='50%';	
	var best_r =rvec[minidx2];	
	var best_t0=t0_vec[idx[minidx2]];
	paramguess2=new Array(2);
	paramguess2[0]=best_r;
	paramguess2[1]=best_t0;
	var checksum=1000000000000000000000000000000000000000000000;
	var best_params=new Array(4);
	document.getElementById("progressbb").style.width='80%';	
	for(var i=0;i<10;i++){
		params=fnminimizer(penalty_logistic2,paramguess2,t,M,0.000005);	
		
		var r = params[0];
		var t0= params[1];	
		//var r = best_r;
		//var t0 = best_t0;
		var h=numeric.div(1,numeric.add(1,numeric.exp(numeric.mul(-1*r,numeric.sub(t,t0)))));
		var K=numeric.div(numeric.dotVV(h,M),numeric.dotVV(h,h));
		var val=logistic_func2(tt,K,r,t0);
		var best_ad=M[0]-val[0];
		paramguess=new Array(4);
		paramguess[0]=K;
		paramguess[1]=r;
		paramguess[2]=t0;
		paramguess[3]=best_ad;
		params=fnminimizer(penalty_logistic3,paramguess,t,M,0.0000001);
		var Mno = penalty_logistic3(params,t,M);	
		if(Mno<checksum){
			best_params=params;
			checksum=Mno;
		}
	}
	
	params=best_params;
	document.getElementById("progressbb").style.width='90%';	
	K =params[0];
	r =params[1];
	t0=params[2];
	ad=params[3];
	//alert("K: "+K+", r: "+r+", t0: "+t0+", ad: "+ad);	
	alert(params);
	var fndata=logistic_func(t,K,r,t0,ad);	
	
	$("#loadin").text("Loading plot/Running calculations...");
	document.getElementById("progressbb").style.width='100%';	
	window.setTimeout(plotgraph(params,t,M,tt,g,fndata,pname,xname,yname),100);	
	window.setTimeout(apptable(t,M,fndata),100);
    $("#bottomlevel").slideDown('fast');  
    window.setTimeout(delayf, 650);	    
	
}

function plotgraph(params,t,M,tt,g,fndata,pname,xname,yname){
	$(".plotinfo").html("Loading...");	
	var checkarray = new Array(t.length);
	var zeros = 0;
	var ones  = 0;
	var twos  = 0;
	var arrgoodt = new Array();
	var arrgoodM = new Array();	
	var arrokt   = new Array();
	var arrokM   = new Array();	
	var arrbadt  = new Array();
	var arrbadM  = new Array();	
	var realbadArray= new Array(1);
	realbadArray[0]="Bad cells:";
	var statbadArray= new Array(1);
	var waitcounter=0;
	var badnumbercheck=0;
	var badnumbercheckhigh=0;
	var badnumberchecklow=0;	
	for(var i=0;i<t.length;i++){
		if(Math.sqrt(Math.pow((M[i]-fndata[i]),2))/fndata[i]<=0.1){
			checkarray[i]=0;
			arrgoodt.push(t[i]);
			arrgoodM.push(M[i]);
			zeros=zeros+1;
			if(badnumbercheckhigh>0){
				waitcounter=waitcounter+1;
			}
			if(waitcounter>2){
				waitcounter=0;
				badnumbercheckhigh=0;
				badnumberchecklow=0;
			}
		}else if(0.3>(Math.sqrt(Math.pow((M[i]-fndata[i]),2))/fndata[i])>0.1){
			checkarray[i]=1;			
			arrokt.push(t[i]);
			arrokM.push(M[i]);	
			ones=ones+1;											
			if(badnumbercheckhigh>0){
				waitcounter=waitcounter+1;
			}
			if(waitcounter>2){
				waitcounter=0;
				badnumbercheckhigh=0;
				badnumberchecklow=0;
			}			
		}else{
			checkarray[i]=2;			
			arrbadt.push(t[i]);
			arrbadM.push(M[i]);
			twos=twos+1;	
			if(badnumbercheckhigh>0&&badnumberchecklow==0){
				if(M[i]<fndata[i]){
					badnumberchecklow=badnumberchecklow+1;
				}
			}else if(badnumbercheckhigh>0&&badnumberchecklow>0){
				if(M[i]<fndata[i]){
					realbadArray.push(t[i-waitcounter-badnumbercheckhigh]);
					badnumbercheckhigh=0;
					badnumberchecklow=0;
				}
			}
			if(M[i]>fndata[i]){
				badnumbercheckhigh=badnumbercheckhigh+1;
				badnumbercheck=badnumbercheck+1;
			}
		}
	}
	var A = new Array(zeros+1);
	var B = new Array(ones+1);
	var C = new Array(twos+1);
	var D = new Array(tt.length+1);
	var H = new Array(M.length+1);
	A[0]=new Array(2);
	B[0]=new Array(2);
	C[0]=new Array(2);		

	
	for(var i=1;i<zeros+1;i++){
		A[i]=new Array(2);
		A[i][0]=arrgoodt[i-1];
		A[i][1]=arrgoodM[i-1];		
	}
	for(var i=1;i<ones+1;i++){
		B[i]=new Array(2);
		B[i][0]=arrokt[i-1];
		B[i][1]=arrokM[i-1];		
	}
	for(var i=1;i<twos+1;i++){
		C[i]=new Array(2);
		C[i][0]=arrbadt[i-1];
		C[i][1]=arrbadM[i-1];		
	}	
	A[0][0]=xname;
	A[0][1]=yname;
	B[0][0]=xname;
	B[0][1]=yname;
	C[0][0]=xname;
	C[0][1]=yname;
	//alert(xname);
	for(var i=0;i<tt.length+1;i++){
		D[i]=new Array(2);
	}
	var fndata=logistic_func(tt,params[0],params[1],params[2],params[3]);
	for(var i=1;i<tt.length+1;i++){
		D[i][0]=tt[i-1];
		D[i][1]=fndata[i-1];
	}	
	for(var i=0;i<M.length+1;i++){
		H[i]=new Array(2);	
	}
	for(var i=1;i<M.length+1;i++){
		H[i][0]=t[i-1];
		H[i][1]=M[i-1];	
	}		
	D[0][0]=xname;
	D[0][1]=yname;
	H[0][0]=xname;
	H[0][1]=yname;
    var data = [
                { label: pname,
                data: D,
                color:"rgb(20,20,20)",
                lines: {show: true},
                points: {show:false},
                clickable:true,
                hoverable:true               
                },
                {label: 'Good Measurement',
                data: A,
                color:"rgb(20,230,20)",
                lines: {show:false},
                points: {show:true},
                clickable:true,
                hoverable:true                
                }, 
                {label: 'Mediocre Measurement',
                data: B,
                color: "orange",
                lines: {show:false},
                points: {show:true},
                clickable:true,
                hoverable:true                
                },
                {label: 'Bad Measurement',
                data: C,
                color: "rgb(230,20,20)",
                lines: {show:false},
                points: {show:true},
                clickable:true,
                hoverable:true                
                }                                           
                ];
                
    
            var options = {
                grid: {
                    hoverable: true,
                    clickable: true},
                legend: {
                    show: true,
                    margin: 10,
                    backgroundOpacity: 0.75
                },
                zoom: {
	                interactive:true
                },
                pan: {
	                interactive:true
                }
            };
    var date = new Date();
    var month = new Array();
	/*month[0] = "January";
	month[1] = "February";
	month[2] = "March";
	month[3] = "April";
	month[4] = "May";
	month[5] = "June";
	month[6] = "July";
	month[7] = "August";
	month[8] = "September";
	month[9] = "October";
	month[10] = "November";
	month[11] = "December";*/
	month[0] = "1";
	month[1] = "2";
	month[2] = "3";
	month[3] = "4";
	month[4] = "5";
	month[5] = "6";
	month[6] = "7";
	month[7] = "8";
	month[8] = "9";
	month[9] = "10";
	month[10] = "11";
	month[11] = "12";	
	var nmon = month[date.getMonth()];
    var dame = date.getDate()+"/"+nmon+"/"+date.getFullYear()+", "+date.getHours()+":"+date.getMinutes()+":"+date.getSeconds();              
    var Gh = JSON.parse(localStorage["collectH"]);
    var Gd = JSON.parse(localStorage["collectD"]);
    var Lh = JSON.parse(localStorage["lengthH"]);    
    var Ld = JSON.parse(localStorage["lengthD"]);
    var Dates = JSON.parse(localStorage["Dates"]);
    var Names = JSON.parse(localStorage["Names"]); 
    var parameters = JSON.parse(localStorage["params"]);    
    var lengs = JSON.parse(localStorage["lengs"]);    
    var plotnames = JSON.parse(localStorage["Plotname"]);        
    localStorage.setItem("check",true);    
	Gh = Gh.concat(H);
	Gd = Gd.concat(D);
	parameters = parameters.concat(params);	
	lengs = lengs.concat(params.length);		
	Lh.push(M.length+1);
	Ld.push(tt.length+1);	
	Dates.push(dame);
	Names.push(g);	
	plotnames.push(pname);
	localStorage["collectD"]=JSON.stringify(Gd);
	localStorage["collectH"]=JSON.stringify(Gh);	
	localStorage["lengthH"]=JSON.stringify(Lh);	
	localStorage["lengthD"]=JSON.stringify(Ld);
	localStorage["Dates"]=JSON.stringify(Dates);	
	localStorage["Names"]=JSON.stringify(Names);	
	localStorage["params"]=JSON.stringify(parameters);	
	localStorage["lengs"]=JSON.stringify(lengs);		
	localStorage["Plotname"]=JSON.stringify(plotnames);			
	if(navigator.onLine){         
    drawingChart(D);     
    }else{
	    alert("No internet connection: Error plotting Google Chart!");
    }
      
    $(".plotinfo").slideDown('fast');
    $(".plotinfo2").slideDown('fast');    	
	var pg = $("#flotplot");
	var cv = $("#canvasplot");	
	var height=$(window).height();
	var width=$(window).width();	
	pg.css("width", width/1.1); 	
	pg.css("heigth", height/1.1); 
	cv.css("width", width/1.1); 	
	cv.css("heigth", height/1.1);     
	var Bad_count=C.length;
	var Bad_count2=C.length-1;	
	var output_issues="";
	for(var i=1;i<Bad_count;i++){
		if(i==Bad_count-1){
			output_issues=output_issues+C[i][0].toString();
		}else{
			output_issues=output_issues+C[i][0].toString()+", ";			
		}
	}
	var plot = $.plot($("#flotplot"),
	data,
	options);				
    $("#flotplot").bind("plotclick", function(event, pos, item){
		if(item){
			$(".plotinfo").html("x: "+xname +": "+ item.datapoint[0].toFixed(2) + '<br/>'+"y: "+yname+": "+ item.datapoint[1].toFixed(2));
			$(".plotinfo").css("color",item.series.color);
			$(".plotinfo").css("border-color",item.series.color);			
			}
		});
	if(C.length>2){
		if(badnumbercheck/M.length>0.5){
			$(".plotinfo2").html("The following issues have been found:"+'<br/>'+Bad_count2.toString()+" Anomalies at:"+'<br/>'+output_issues+'<br/>'+"Suggested Prediction: Systematic error!");
		}else if(realbadArray.length>1){
			$(".plotinfo2").html("The following issues have been found:"+'<br/>'+Bad_count2.toString()+" Anomalies at:"+'<br/>'+output_issues+'<br/>'+"Suggested Prediction: Culture dying, starting at x:"+realbadArray[1].toString()+"!");
		}else{
			$(".plotinfo2").html("The following issues have been found:"+'<br/>'+Bad_count2.toString()+" Anomalies at x-Values:"+'<br/>'+output_issues+'<br/>'+"Suggested Prediction: Random Bad Measurements");		
		}
	}else if(C.length==2){
		$(".plotinfo2").html("The following issues have been found:"+'<br/>'+Bad_count2.toString()+" Anomaly at:"+'<br/>'+output_issues+'<br/>'+"Suggested Prediction: Singular Random Bad Measurement");		
	}else{
		$(".plotinfo2").html("The following issues have been found:"+'<br/>'+"None!");		
	}
}
function apptable(t,M,fndata){
	$("#datatable td").remove();
	var mean = 0;    
	
	for(var i=0;i<fndata.length;i++){
		mean = mean+Math.sqrt(Math.pow(M[i]-fndata[i],2));
	}	
	for(var i=0;i<t.length;i++){
		if(Math.sqrt(Math.pow((M[i]-fndata[i]),2))/fndata[i]<=0.1){
			$("#datatable").find('tbody').append($('<tr class="success">').append($('<td>').text((i+1).toString())).append($('<td>').text(t[i].toString())).append($('<td>').text(M[i].toString())).append($('<td>').text("04/12/2013")).append($('<td>').text("Good")));	
		}else if(0.5>(Math.sqrt(Math.pow((M[i]-fndata[i]),2))/fndata[i])>0.1){
			$("#datatable").find('tbody').append($('<tr class="warning">').append($('<td>').text((i+1).toString())).append($('<td>').text(t[i].toString())).append($('<td>').text(M[i].toString())).append($('<td>').text("04/12/2013")).append($('<td>').text("Ok")));			
		}else{
			$("#datatable").find('tbody').append($('<tr class="danger">').append($('<td>').text((i+1).toString())).append($('<td>').text(t[i].toString())).append($('<td>').text(M[i].toString())).append($('<td>').text("04/12/2013")).append($('<td>').text("Bad")));			
		}
    } 	
    $("#dtb").css("width",$(window).width()/1.8);    
    $("#container").slideDown('fast');	
}

function delayf(){
	$("#loadin").text("Loading table...");
	$(".plotinfo").html("No points selected!");	
    window.setTimeout(delayf2, 700);			

}
function delayf2(){
	$("#progressb").hide();	
	document.getElementById("progressbb").style.width='0%';	
	$("#block").hide();
}

function drawingChart(H){
    google.load("visualization", "1", {packages:["corechart"],callback: drawChart});
    google.setOnLoadCallback(drawChart);
    
    function drawChart() {
        console.log("drawChart");
        var data = google.visualization.arrayToDataTable(H);
 
        var options = {
            title: "Google Chart - Cellproliferation",
            vAxis: {title: "Concentration [Cells/ml]"},
            hAxis: {title: "Time [h]"}
        };
 
        var chart = new google.visualization.LineChart(document.getElementById('gcchart'));
        chart.draw(data, options);}
     $("#gcontainer").show();
}