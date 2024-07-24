//
// Generic Sakuma theorem: non-symmetric case
// construction of the universal algebra
//
// (c) 2020 C. Franchi, M. Mainardis, S. Shpectorov
//
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

ring F=(0,al,bt),( lm, lmf, lm2, lm2f), dp;
freemodule(8);
vector am2=gen(1);
vector am1=gen(2);
vector a0=gen(3);
vector a1=gen(4);
vector a2=gen(5);
vector s1=gen(6);
vector s2=gen(7);
vector s2f=gen(8);
list a=am2,am1,a0,a1,a2,s1,s2,s2f;
list r=0,0,0,0,0,0,0,0;
list Mult=r,r,r,r,r,r,r,r;

Mult[1][1]=am2; Mult[2][2]=am1; Mult[3][3]=a0; Mult[4][4]=a1; Mult[5][5]=a2; 

vector m12=s1+bt*(a[1]+a[2]);
vector m23=s1+bt*(a[2]+a[3]);
vector m34=s1+bt*(a[3]+a[4]);
vector m45=s1+bt*(a[4]+a[5]);
vector m13=s2+bt*(a[1]+a[3]);
vector m35=s2+bt*(a[3]+a[5]);
vector m24=s2f+bt*(a[2]+a[4]);

Mult[1][2]= m12; Mult[2][1]=m12;  Mult[1][3]= m13; Mult[3][1]=m13; Mult[2][3]= m23; Mult[3][2]=m23;  Mult[3][4]= m34; Mult[4][3]=m34;  Mult[4][5]= m45; Mult[5][4]=m45;  Mult[3][5]= m35; Mult[5][3]=m35;    Mult[2][4]= m24; Mult[4][2]=m24;  

vector m26=(al-bt)*a[6]+(lmf*(1-al)+bt*(al-bt-1))*a[2]+
  (1/2)*(al-bt)*bt*(a[1]+a[3]);
vector m36=(al-bt)*a[6]+(lm*(1-al)+bt*(al-bt-1))*a[3]+
  (1/2)*(al-bt)*bt*(a[2]+a[4]);
vector m46=(al-bt)*a[6]+(lmf*(1-al)+bt*(al-bt-1))*a[4]+
  (1/2)*(al-bt)*bt*(a[3]+a[5]);
vector m37=(al-bt)*a[7]+(lm2*(1-al)+bt*(al-bt-1))*a[3]+
  (1/2)*(al-bt)*bt*(a[1]+a[5]);
  
Mult[2][6]= m26; Mult[6][2]=m26; Mult[3][6]= m36; Mult[6][3]=m36;  Mult[4][6]= m46; Mult[6][4]=m46; Mult[3][7]= m37; Mult[7][3]=m37; 
 
proc Times (vector u, vector v)
{
vector ans=[0];
list rem=list();
 for(int i=1; i<=8; i=i+1)
  { if (u[i]<>0)
     {
        for(int j=1; j<=8; j=j+1)
          {
              if (v[j]<>0)
               { if (Mult[i][j]<>0*a[1])
                   {
                   ans=ans+u[i]*v[j]*Mult[i][j];
                   }
                   else
                  { list l=list(i,j), u[i]*v[j];
                      rem=rem+l;
                   }             
          }  
     }
  }
  }
    if (size(rem)==0)
       {   return(ans);
           }
   else
       {list k=ans, rem;
      return(k);}
}

// Symmetries

proc tau0 (vector v)
  {
    return(v[5]*a[1]+v[4]*a[2]+v[3]*a[3]+v[2]*a[4]+v[1]*a[5]+v[6]*a[6]+v[7]*a[7]+v[8]*a[8]);        
  }  
 
map ff=F, lmf,lm, lm2f, lm2;

proc fold (vector v)
{
poly v1=v[1];
poly v2=v[2];
poly v3=v[3];
poly v4=v[4];
poly v5=v[5];
poly v6=v[6];
poly v7=v[7];
poly v8=v[8];
poly ffv2=ff(v2); 
poly ffv3=ff(v3);
poly ffv4= ff(v4); 
poly ffv5=ff(v5); 
poly ffv6=ff(v6); 
poly ffv7=ff(v7); 
poly ffv8=ff(v8);

if (v1==0)
       {vector s=ffv5*a[2]+ffv4*a[3]+ffv3*a[4]+ffv2*a[5]+ffv6*a[6]+ffv8*a[7]+ffv7*a[8];
        return(s);}
        else
          {return("fail");}
          } 
          
proc lambda (vector v)
{
 if (v[8]==0) 
  { poly p= lm2*v[1]+lm*v[2]+v[3]+lm*v[4]+lm2*v[5]+(lm-bt-bt*lm)*v[6]+(lm2-bt-bt*lm2)*v[7];
  return(p); }
else
          {return("fail");}
}        
 
vector v1= (s1+(bt-lm)*a0+(bt/2)*(a1+am1))/al; // 
vector u1=a1-lm*a0-v1-(a1-am1)/2;  // 

vector uu=Times(u1, u1)[1];  
vector uv=Times(u1, v1)[1]; 
vector vv=Times(v1, v1)[1]; 

// (uu+uv) is a 0-eigenvector for a0 and contains s2f: we compute lambda(s2f)

vector w=(uu+uv)-(uu+uv)[8]*s2f;
 
poly ls2f=-lambda(w)/((uu+uv)[8]);

// update lambda

proc lambda (vector v)
{
   poly p= lm2*v[1]+lm*v[2]+v[3]+lm*v[4]+lm2*v[5]+(lm-bt-bt*lm)*v[6]+(lm2-bt-bt*lm2)*v[7]+ls2f*v[8];
  return(p); 
  } 
  
// u1*u1 is a 0-eigenvector for a0, hence it has 0-projection on a0, and it contains 1/(al^2)*s1*s1 

poly ls1s1=-(al^2)*lambda(uu);; // lambda(s1*s1)

//
// Express a0*s2f
//
vector w=uu-vv -lambda(uu-vv)*a0; // this is a 0-eigenvector for a0
// Times(a0, w)  this vector must be zero
// it involves a0*s2f with coefficient (al-2*bt)/(2*al), hence we can express a0*s2f

Mult[3][8]=-2*al*Times(a0, w)[1]/(al-2*bt);
Mult[8][3]=Mult[3][8];

//
// Express s1*s1
//

// a0*(u1*u1+u1*v1)=al*u1*v1, where the right side has -s1*s1/al

vector s1s1=-al*(Times(a0,uu+uv)-al*uv);
Mult[6][6]=s1s1;

//
// Express a3 and am3
//

// s1*s1 contains am2 times bt*(al-bt)^2*(al-4*bt)/(4*(al-2*bt))
//
// so fold(s1*s1)-s1*s1=0 and it contains a3 times the same

vector A3=-4*(al-2*bt)*(fold(s1s1-bt*((al-bt)^2)*
     (al-4*bt)*am2/(4*(al-2*bt)))-s1s1)/
     (bt*((al-bt)^2)*(al-4*bt));
     
// Update function f

proc f (vector v)
{
poly v1=v[1];
poly v2=v[2];
poly v3=v[3];
poly v4=v[4];
poly v5=v[5];
poly v6=v[6];
poly v7=v[7];
poly v8=v[8];
poly ffv1=ff(v1);
poly ffv2=ff(v2); 
poly ffv3=ff(v3);
poly ffv4= ff(v4); 
poly ffv5=ff(v5); 
poly ffv6=ff(v6); 
poly ffv7=ff(v7); 
poly ffv8=ff(v8);
       vector s=ffv1*A3+ffv5*a[2]+ffv4*a[3]+ffv3*a[4]+ffv2*a[5]+ffv6*a[6]+ffv8*a[7]+ffv7*a[8];
        return(s);
          } 
     
// Express am3 and a4

vector Am3=tau0(A3);
vector A4=f(Am3);

// Define tau1

proc tau1(vector v)
{
vector s=v[1]*A4+v[2]*A3+v[3]*a2+v[4]*a1+v[5]*a0+v[6]*s1+v[7]*s2+v[8]*s2f;
 return(s); 
}

// Add products with s1

Mult[1][6]=(al-bt)*s1+(lm*(1-al)+bt*(al-bt-1))*a[1]+(1/2)*(al-bt)*bt*(Am3+a[2]);
Mult[6][1]=Mult[1][6];
Mult[5][6]=(al-bt)*s1+(lm*(1-al)+bt*(al-bt-1))*a[5]+(1/2)*(al-bt)*bt*(a[4]+A3);
Mult[6][5]=Mult[5][6];

//
// Obtaining relations on al, bt, lm, lmf for given lm2 and lm2f
//
// Express S3_0, S3_1, S3_2

vector S3_0=Times(a0,A3)-bt*(a0+A3);
vector S3_1=f(S3_0);
vector S3_2=tau1(S3_0);

// D=<tau0,f> should induce D_6 on {S3_0,S3_1,S3_2}
// hence the following must be relations

vector diff0=S3_2-tau0(S3_1);
vector diff1=f(diff0);
vector diff2=tau1(diff0);

vector doublediff0=tau0(diff0)-diff0;;
vector doublediff1=tau0(diff1)-diff1;; // seems to be equal to -doublediff0
vector doublediff2=tau0(diff2)-diff2;;

// here are some polynomial relations

poly poly1=lambda(diff0); // poly 1 in the paper
poly poly2=lambda(diff2); // 

// function lambdb
proc lambdb(vector v)
{
poly l=lambda(f(v));
 return(ff(l)); 
}

poly  poly3=lambdb(diff0); // poly 3 in the paper


// complete the multiplication table

Mult[4][7]=f(Mult[3][8]);;
Mult[7][4]=Mult[7][4];;

Mult[2][7]=tau0(Mult[4][7]);;
Mult[7][2]=Mult[2][7];;

Mult[5][8]=f(Mult[2][7]);;
Mult[8][5]=Mult[5][8];;

Mult[1][8]=tau0(Mult[5][8]);;
Mult[8][1]=Mult[1][8];;

Mult[4][8]=f(Mult[3][7]);;
Mult[8][4]=Mult[4][8];;

Mult[2][8]=tau0(Mult[4][8]);;
Mult[8][2]=Mult[2][8];;

Mult[5][7]=tau1(Mult[3][7]);;
Mult[7][5]=Mult[5][7];;

Mult[1][7]=tau0(Mult[5][7]);;
Mult[7][1]=Mult[1][7];;

Mult[4][7]=tau0(Mult[2][7]);;
Mult[7][4]=Mult[4][7];;

Mult[1][4]=f(Times(a0, A3));;
Mult[4][1]=Mult[1][4];;

Mult[2][5]=tau0(Mult[1][4]);;
Mult[5][2]=Mult[2][5];

Mult[1][5]=f(tau0(f(Times(a0, A4))));;
Mult[5][1]=Mult[1][5];;

vector u2=-s2+(lm2-bt-al*lm2)*a0+((al-bt)/2)*(a2+am2);;  
vector v2=s2+(bt-lm2)*a0+bt*(a2+am2)/2;;  

vector u1u2=Times(u1, u2)[1]; // contains [6][7] with coefficient 1/al
vector v1u2=Times(v1, u2)[1]; // contains [6][7] with coefficient -1/al

// we obtain the products s1*s2,  s1*s2f, and s2*s2 with the method described in Proposition 5.10
vector p12=u1u2+v1u2;;
Mult[6][7]=al*Times(v1, u2)[1]-Times(a0, p12);;
Mult[7][6]=Mult[6][7];; 
Mult[6][8]=f(Mult[6][7]);;
Mult[8][6]=Mult[6][8];; 

vector u2u2=Times(u2, u2)[1];; // contains [7][7] with coefficient 1
vector v2u2=Times(v2, u2)[1];; // contains [7][7] with coefficient -1
vector p22=u2u2+v2u2;;
Mult[7][7]=Times(v2, u2)[1]-Times(a0, p22)/al;;
Mult[8][8]=f(Mult[7][7]);;

// finally we compute s2*s2f. A3*A3-A3 must be the zero vector and it contains s2*s2f

Mult[7][8]=(A3-Times(A3,A3)[1])/(2*Times(A3,A3)[2][2]);;
Mult[8][7]=Mult[7][8];;

//////// one more polynomial

poly poly4=lambda(Times(A4,A4)-A4); // poly 2 in the paper
poly poly4=ff(Times(A4,A4)-A4); // poly 4 in the paper



map val=F, lm, lm, lm2, lm2;
poly q1=val(poly1);
poly q2=val(poly4);


// Check for the proof of Lemma 6.4

factorize(resultant(q1,q2,lm2)); // we get the five values for lm: 1, 0, bt/2, al/2, (3*al^2+3*al*bt-al-2*bt)/(8*al-4)
factorize(resultant(q1,q4,lm2)); // we get the five values for lm: 1, 0, bt/2, al/2, (3*al^2+3*al*bt-al-2*bt)/(8*al-4)


// we compute the respective values of lm2
map val1=F, 1,1, lm2,lm2;
factorize(val1(q1)); 
factorize(val1(q2)); // we get lm2=1 

map val2=F, 0,0, lm2,lm2; 
factorize(val2(q1));  
factorize(val2(q2));  // we get lm2=1

map val3=F, bt/2,bt/2, lm2,lm2; 
factorize(val3(q1));  
factorize(val3(q2));  // we get lm2=bt/2

map val4=F, al/2,al/2, lm2,lm2; 
factorize(val4(q1));  
factorize(val4(q2));  // we get lm2=1

map val5=F, (3*al^2+3*al*bt-al-2*bt)/(8*al-4), (3*al^2+3*al*bt-al-2*bt)/(8*al-4), lm2,lm2; 
factorize(val5(q1));  
factorize(val5(q2));  // we get lm2=(3*al^2+3*al*bt-al-2*bt)/(8*al-4)

// Check for the proof of Lemma 6.5

list L= 1, 0, bt/2, al/2, (3*al^2+3*al*bt-al-2*bt)/(8*al-4);

// we define some auxiliary functions
// valuation mapL for a polynomial in the case lm2=L[i], lm2f=L[j]

proc mapL(int i, int j) 
 { 
    map m = F, lm, lmf, L[i],L[j];
    return(m);
    }

// given two lists of polynomials (of degree 1) l1 and l2 , samep returns the  polynomials that are, up to a scalar, in the intersection of l1 with l2
    
proc  samep(list l1, list l2) 
{ 
list good=list();
 for (int i=1; i<=size(l1); i=i+1)
     {
	for (int j=1; j<=size(l2); j=j+1)	  	
	   {
               if (resultant(l1[i], l2[j], lm)==0*al) 
		{   
		list LL = l1[i];
	           good=good+LL;
		}
	    }
      }
      return(good);
      }

// given the polynomials pol1 and pol2, degone returns the list of  factors of degree 1 of the resultant of mapL(i,j)(pol1) and mapL(i,j)(pol2) with respect to lmf
      
proc degone(int i, int j, poly pol1, poly pol2) 
{
   list Fact=list();
   list fact = factorize(resultant(mapL(i,j)(pol1), mapL(i,j)(pol2), lmf))[1];
      for (int k = 2; k<= size(fact[1]); k=k+1)
	  {
	       if ( deg(fact[1][k])==1) 
			{
			     list l=fact[1][k];
			     Fact=Fact+l;
			     }
			     }
   return(Fact);
   }

// commonf returns the common factors of degree 1 of the resultants with respect to lmf of  mapL(i,j)(pol1) and mapL(i,j)(pol2), and mapL(i,j)(pol1) and mapL(i,j)(pol3)

 
proc commonf(int i, int j, poly pol1, poly pol2, poly pol3) {   
   return(samep(degone(i,j, pol1, pol2), degone(i,j, pol1, pol3)));
   }

// for 1<=i,j<=5 we compute the common factors of degree 1 of the resultants with respect to lmf of the polinomyals poly1, poly4, and poly1, poly3 evaluated for lm2=L[i], lm2f=L[j].
    
  for (int i = 1; i <= 5; i=i+1)
       { 
        for (int j = 1; j<= 5; j=j+1)
         {
            list l=L[i],L[j],commonf(i,j,poly1, poly4, poly3);
            print( l );
            } 
        }

// results					
[1]:
   1
[2]:
   1
[3]:
   [1]:
      2*lm+(-al)
   [2]:
      lm-1
   [3]:
      lm
// ** redefining l (            list l=L[i],L[j],commonf(i,j,poly1, poly2, poly3);)
[1]:
   1
[2]:
   0
[3]:
   [1]:
      lm
// ** redefining l (            list l=L[i],L[j],commonf(i,j,poly1, poly2, poly3);)
[1]:
   1
[2]:
(bt)/2
[3]:
   [1]:
      lm
// ** redefining l (            list l=L[i],L[j],commonf(i,j,poly1, poly2, poly3);)
[1]:
   1
[2]:
(al)/2
[3]:
   [1]:
      lm
// ** redefining l (            list l=L[i],L[j],commonf(i,j,poly1, poly2, poly3);)
[1]:
   1
[2]:
(3*al^2+3*al*bt-al-2*bt)/(8*al-4)
[3]:
   [1]:
      lm
// ** redefining j (int j = 1;)
// ** redefining l (            list l=L[i],L[j],commonf(i,j,poly1, poly2, poly3);)
[1]:
   0
[2]:
   1
[3]:
   empty list
// ** redefining l (            list l=L[i],L[j],commonf(i,j,poly1, poly2, poly3);)
[1]:
   0
[2]:
   0
[3]:
   empty list
// ** redefining l (            list l=L[i],L[j],commonf(i,j,poly1, poly2, poly3);)
[1]:
   0
[2]:
(bt)/2
[3]:
   empty list
// ** redefining l (            list l=L[i],L[j],commonf(i,j,poly1, poly2, poly3);)
[1]:
   0
[2]:
(al)/2
[3]:
   empty list
// ** redefining l (            list l=L[i],L[j],commonf(i,j,poly1, poly2, poly3);)
[1]:
   0
[2]:
(3*al^2+3*al*bt-al-2*bt)/(8*al-4)
[3]:
   empty list
// ** redefining j (int j = 1;)
// ** redefining l (            list l=L[i],L[j],commonf(i,j,poly1, poly2, poly3);)
[1]:
(bt)/2
[2]:
   1
[3]:
   empty list
// ** redefining l (            list l=L[i],L[j],commonf(i,j,poly1, poly2, poly3);)
[1]:
(bt)/2
[2]:
   0
[3]:
   empty list
// ** redefining l (            list l=L[i],L[j],commonf(i,j,poly1, poly2, poly3);)
// ** redefining j (int j=1;)
[1]:
(bt)/2
[2]:
(bt)/2
[3]:
   [1]:
      2*lm+(-bt)
// ** redefining l (            list l=L[i],L[j],commonf(i,j,poly1, poly2, poly3);)
[1]:
(bt)/2
[2]:
(al)/2
[3]:
   empty list
// ** redefining l (            list l=L[i],L[j],commonf(i,j,poly1, poly2, poly3);)
[1]:
(bt)/2
[2]:
(3*al^2+3*al*bt-al-2*bt)/(8*al-4)
[3]:
   empty list
// ** redefining j (int j = 1;)
// ** redefining l (            list l=L[i],L[j],commonf(i,j,poly1, poly2, poly3);)
[1]:
(al)/2
[2]:
   1
[3]:
   empty list
// ** redefining l (            list l=L[i],L[j],commonf(i,j,poly1, poly2, poly3);)
[1]:
(al)/2
[2]:
   0
[3]:
   empty list
// ** redefining l (            list l=L[i],L[j],commonf(i,j,poly1, poly2, poly3);)
[1]:
(al)/2
[2]:
(bt)/2
[3]:
   empty list
// ** redefining l (            list l=L[i],L[j],commonf(i,j,poly1, poly2, poly3);)
[1]:
(al)/2
[2]:
(al)/2
[3]:
   empty list
// ** redefining l (            list l=L[i],L[j],commonf(i,j,poly1, poly2, poly3);)
[1]:
(al)/2
[2]:
(3*al^2+3*al*bt-al-2*bt)/(8*al-4)
[3]:
   empty list
// ** redefining j (int j = 1;)
// ** redefining l (            list l=L[i],L[j],commonf(i,j,poly1, poly2, poly3);)
[1]:
(3*al^2+3*al*bt-al-2*bt)/(8*al-4)
[2]:
   1
[3]:
   empty list
// ** redefining l (            list l=L[i],L[j],commonf(i,j,poly1, poly2, poly3);)
[1]:
(3*al^2+3*al*bt-al-2*bt)/(8*al-4)
[2]:
   0
[3]:
   empty list
// ** redefining l (            list l=L[i],L[j],commonf(i,j,poly1, poly2, poly3);)
[1]:
(3*al^2+3*al*bt-al-2*bt)/(8*al-4)
[2]:
(bt)/2
[3]:
   empty list
// ** redefining l (            list l=L[i],L[j],commonf(i,j,poly1, poly2, poly3);)
[1]:
(3*al^2+3*al*bt-al-2*bt)/(8*al-4)
[2]:
(al)/2
[3]:
   empty list
   
[1]:
(3*al^2+3*al*bt-al-2*bt)/(8*al-4)
[2]:
(3*al^2+3*al*bt-al-2*bt)/(8*al-4)
[3]:
   [1]:
      (8*al-4)*lm+(-3*al^2-3*al*bt+al+2*bt)   
   
	
// case (1,lmf,1,1)
map m1=F, 1, lmf, 1,1; // get lmf=1
factorize(m1(poly1));
// case (0,lmf,1,1)
map m2=F, 0, lmf, 1,1; // get lmf=1
factorize(m2(poly3));
// case (al/2,lmf,1,1)
map m3=F, al/2, lmf, 1,1; // get lmf=al/2
factorize(m3(poly1));
// case (0,lmf,1,0)
map m4=F, 0, lmf, 1,0; // get no lmf
factorize(m4(poly3));
// case (0,lmf,1,bt/2)
map m5=F, 0, lmf, 1,bt/2; // get no lmf
factorize(m5(poly3));
// case (0,lmf,1,al/2)
map m6=F, 0, lmf, 1,al/2; // get no lmf
factorize(m6(poly3));
// case (0,lmf,1,(3*al^2+3*al*bt-al-2*bt)/(8*al-4))
map m7=F, 0, lmf, 1,(3*al^2+3*al*bt-al-2*bt)/(8*al-4); // get no lmf
factorize(m7(poly3));
// case (bt/2,lmf,bt/2,bt/2)
map m8=F, bt/2, lmf, bt/2,bt/2; // get lmf=bt/2
factorize(m8(poly1));
// case ((3*al^2+3*al*bt-al-2*bt)/(8*al-4),lmf,(3*al^2+3*al*bt-al-2*bt)/(8*al-4),(3*al^2+3*al*bt-al-2*bt)/(8*al-4))
map m9=F, (3*al^2+3*al*bt-al-2*bt)/(8*al-4), lmf, (3*al^2+3*al*bt-al-2*bt)/(8*al-4),(3*al^2+3*al*bt-al-2*bt)/(8*al-4); 
factorize(m9(poly1)); // get lmf=(3*al^2+3*al*bt-al-2*bt)/(8*al-4)

/////////////////////////////////////////////////////////
// proof of Theorem 1.3

// value return the image of the vector v when we set lm=poly1, lmf=poly2, pl2=poly3, lm2f=poly4

proc value(poly p1, poly p2, poly p3, poly p4, vector v)
 { 
 poly v1=v[1];
 poly v2=v[2];
 poly v3=v[3];
 poly v4=v[4];
 poly v5=v[5];
 poly v6=v[6];
 poly v7=v[7];
 poly v8=v[8];
     map m=F, p1, p2, p3, p4;
     return( m(v1)*am2+m(v2)*am1+m(v3)*a0+m(v4)*a1+m(v5)*a2+m(v6)*s1+m(v7)*s2+m(v8)*s2f);
  }

// 
// Determination of the algebras U_P for the different choices of P
// case P=(bt/2, bt/2, bt/2, bt/2)

value(bt/2, bt/2, bt/2, bt/2, doublediff0); // the coefficient of am2 is <>0

vector Am2=-(value(bt/2, bt/2, bt/2, bt/2, doublediff0)-value(bt/2, bt/2, bt/2, bt/2, doublediff0)[1]*am2)/value(bt/2, bt/2, bt/2, bt/2, doublediff0)[1]; // we get Am2=a2+a1-am1

proc update(vector v)
  { 
  return( v-v[1]*am2+v[1]*Am2);
  }

vector S2f=-(value(bt/2, bt/2, bt/2, bt/2, update(diff0))-value(bt/2, bt/2, bt/2, bt/2, update(diff0))[8]*s2f)/value(bt/2, bt/2, bt/2, bt/2, update(diff0))[8]; 

proc update(vector v)
  { 
  return( v-v[1]*am2+v[1]*Am2-v[8]*s2f+v[8]*S2f);
  }
  
vector A2=-(value(bt/2, bt/2, bt/2, bt/2, update(diff2))-value(bt/2, bt/2, bt/2, bt/2, update(diff2))[5]*a2)/value(bt/2, bt/2, bt/2, bt/2, update(diff2))[5]; // A2=am1 whence Am2=a1 and s2=s1, whence s2f=s2

proc update(vector v)
  { 
  return( v-v[1]*am2+v[1]*a1-v[8]*s2f+v[8]*s1-v[5]*a2+v[5]*am1-v[7]*s2+v[7]*s1);
  }

// the following vector C must be 0  
vector C=update(value(bt/2, bt/2, bt/2, bt/2,update(Times(s2,s1)-Times(s1,s1))));  
// from here we get s1=-bt/2*(am1+a0+a1)


// Case P=((3*al^2+3*al*bt-al-2*bt)/(8*al-4), (3*al^2+3*al*bt-al-2*bt)/(8*al-4), (3*al^2+3*al*bt-al-2*bt)/(8*al-4), (3*al^2+3*al*bt-al-2*bt)/(8*al-4))

poly nu=(3*al^2+3*al*bt-al-2*bt)/(8*al-4);

value(nu, nu, nu, nu, doublediff0); // the coefficient of am2 is <>0

vector Am2=-(value(nu, nu, nu, nu, doublediff0)-value(nu, nu, nu, nu, doublediff0)[1]*am2)/value(nu, nu, nu, nu, doublediff0)[1]; // we get Am2=a2+a1-am1

proc update(vector v)
  { 
  return( v-v[1]*am2+v[1]*Am2);
  }

vector S2f=-(value(nu, nu, nu, nu, update(diff0))-value(nu, nu, nu, nu, update(diff0))[8]*s2f)/value(nu, nu, nu, nu, update(diff0))[8]; 

proc update(vector v)
  { 
  return( v-v[1]*am2+v[1]*Am2-v[8]*s2f+v[8]*S2f);
  }
  
vector A2=-(value(nu, nu, nu, nu, update(diff2))-value(nu, nu, nu, nu, update(diff2))[5]*a2)/value(nu, nu, nu, nu, update(diff2))[5]; // A2=am1

// case P=(al/2, al/2, 1,1)

value(al/2, al/2, 1, 1, doublediff0); // the coefficient of am2 is <>0

vector Am2=-(value(al/2, al/2, 1, 1, doublediff0)-value(al/2, al/2, 1, 1, doublediff0)[1]*am2)/value(al/2, al/2, 1, 1, doublediff0)[1]; // 

proc update(vector v)
  { 
  return( v-v[1]*am2+v[1]*Am2);
  }

vector S2f=-(value(al/2, al/2, 1,1, update(diff0))-value(al/2, al/2, 1, 1, update(diff0))[8]*s2f)/value(al/2, al/2, 1, 1, update(diff0))[8]; 

proc update(vector v)
  { 
  return( v-v[1]*am2+v[1]*Am2-v[8]*s2f+v[8]*S2f);
  }
 
value(al/2, al/2, 1,1, update(doublediff2))/value(al/2, al/2, 1,1, update(doublediff2))[2];  // am1-a1
value(al/2, al/2, 1,1, update(diff2))/value(al/2, al/2, 1,1, update(diff2))[2];  // am1+a0-a1-a2

// case P=(0, 0, 1,1)

value(0, 0, 1, 1, doublediff0); // the coefficient of am2 is <>0

vector Am2=-(value(0, 0, 1, 1, doublediff0)-value(0, 0, 1, 1, doublediff0)[1]*am2)/value(0, 0, 1, 1, doublediff0)[1]; // 

proc update(vector v)
  { 
  return( v-v[1]*am2+v[1]*Am2);
  }

vector S2f=-(value(0,0, 1,1, update(diff0))-value(0,0,1,1, update(diff0))[8]*s2f)/value(0, 0, 1, 1, update(diff0))[8]; 

proc update(vector v)
  { 
  return( v-v[1]*am2+v[1]*Am2-v[8]*s2f+v[8]*S2f);
  }
 
value(0,0, 1,1, update(doublediff2))/value(0,0, 1,1, update(doublediff2))[2];  // am1-a1
value(0,0, 1,1, update(diff2))/value(0,0, 1,1, update(diff2))[2];  // am1+a0-a1-a2

proc update(vector v)
  { 
  return( v-v[1]*am2+v[1]*a0-v[2]*am1+v[2]*a1-v[5]*a2+v[5]*a0-v[7]*s2+v[7]*(1-2*bt)*a0-v[8]*s2f+v[8]*(1-2*bt)*a1);
  }

vector C1=value(0,0,1,1, Times(a0, (1-2*bt)*a1))-value(0,0,1,1,update(Times(a0, s2f)));
vector S1=-(C1-C1[6]*s1)/C1[6];

// case P=(1,1, 1,1)

value(1,1, 1, 1, doublediff0); // the coefficient of am2 is <>0

vector Am2=-(value(1,1, 1, 1, doublediff0)-value(1,1, 1, 1, doublediff0)[1]*am2)/value(1,1, 1, 1, doublediff0)[1]; // 

proc update(vector v)
  { 
  return( v-v[1]*am2+v[1]*Am2);
  }

vector S2f=-(value(1,1, 1,1, update(diff0))-value(1,1,1,1, update(diff0))[8]*s2f)/value(1,1, 1, 1, update(diff0))[8]; 

proc update(vector v)
  { 
  return( v-v[1]*am2+v[1]*Am2-v[8]*s2f+v[8]*S2f);
  }

// vector d2 
value(1,1, 1,1, update(doublediff2))/value(1,1, 1,1, update(doublediff2))[2];  // am1-a1, hence s2f=(1-2*bt)*a1 and s2=(1-2*bt)*a0

proc update(vector v)
  { 
  return( v-v[1]*am2+v[1]*Am2-v[8]*s2f-v[8]*(1-2*bt)*a1-v[2]*am1+v[2]*a1-v[7]*s2+v[7]*(1-2*bt)*a0);
  }
  
update(Am2); \\ a2  

proc update(vector v)
  { 
  return( v-v[1]*am2+v[1]*a2-v[8]*s2f+v[8]*(1-2*bt)*a1-v[2]*am1+v[2]*a1-v[7]*s2+v[7]*(1-2*bt)*a0);
  }
  
  vector C1=value(1,1,1,1, Times(a0, (1-2*bt)*a1))-value(1,1,1,1,update(Times(a0, s2f)));
  vector S1=-(C1-C1[6]*s1)/C1[6];

// compute diff2-diff2^f

(value(1,1, 1,1, update(diff2))-update(tau1(value(1,1, 1,1, update(diff2)))))/(value(1,1, 1,1, update(diff2))-update(tau1(value(1,1, 1,1, update(diff2)))))[5]; //a2-a0

proc update(vector v)
  { 
  return( v-v[1]*am2+v[1]*a0-v[8]*s2f+v[8]*(1-2*bt)*a1-v[2]*am1+v[2]*a1-v[7]*s2+v[7]*(1-2*bt)*a0-v[5]*a2+v[5]*a0);
  }

// vector d2  
value(1,1, 1,1, update(diff2))/value(1,1, 1,1, update(diff2))[3]; // a0-a1
