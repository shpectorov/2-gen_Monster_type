##################################################
#
# General Sakuma theorem: Symmetric case al=4*bt : lm=(18*bt-1)/8, lm2=(480*bt^3-228*bt^2+28*bt-1)/64*bt^2
#
#
# (c) 2020 C. Franchi, M. Mainardis, S. Shpectorov
#
##################################################
ring F=(0, bt),(lm3), dp;
freemodule(15);
vector am4=gen(1);
vector am3=gen(2);
vector am2=gen(3);
vector am1=gen(4);
vector a0=gen(5);
vector a1=gen(6);
vector a2=gen(7);
vector a3=gen(8);
vector a4=gen(9);
vector s=gen(10);
vector s2=gen(11);
vector s2f=gen(12);
vector s3=gen(13);
vector s3f=gen(14);
vector s3t=gen(15);
list a=am4, am3,am2,am1,a0,a1,a2,a3,a4, s,s2,s2f,s3,s3f, s3t;
poly al=4*bt;
poly lm=(18*bt-1)/8;
poly lmf=lm;
poly lm2=(480*bt^3-228*bt^2+28*bt-1)/(64*bt^2);
poly lm2f=lm2;
poly lm3f=lm3;
poly lm3t=lm3;
list r=0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
list Mult=r,r,r,r,r,r,r,r,r,r,r,r,r,r,r;

Mult[1][1]=am4; Mult[2][2]=am3; Mult[3][3]=am2; Mult[4][4]=am1; Mult[5][5]=a0; Mult[6][6]=a1; Mult[7][7]=a2; Mult[8][8]=a3; Mult[9][9]=a4;

vector m12=s+bt*(am4+am3);
vector m23=s+bt*(am3+am2);
vector m34=s+bt*(am2+am1);
vector m45=s+bt*(am1+a0);
vector m56=s+bt*(a0+a1);
vector m67=s+bt*(a1+a2);
vector m78=s+bt*(a2+a3);
vector m89=s+bt*(a3+a4);


vector m24=s2f+bt*(am3+am1);
vector m46=s2f+bt*(am1+a1);
vector m68=s2f+bt*(a1+a3);

vector m13=s2+bt*(am4+am2);
vector m35=s2+bt*(am2+a0);
vector m57=s2+bt*(a0+a2);
vector m79=s2+bt*(a2+a4);

vector m14=s3t+bt*(am4+am1);
vector m25=s3+bt*(am3+a0);
vector m36=s3f+bt*(am2+a1);
vector m47=s3t+bt*(am1+a2);
vector m58=s3+bt*(a0+a3);
vector m69=s3f+bt*(a1+a4);



vector m410=(al-bt)*s+(lmf*(1-al)+bt*(al-bt-1))*am1+
  (1/2)*(al-bt)*bt*(am2+a0);
vector m510=(al-bt)*s+(lm*(1-al)+bt*(al-bt-1))*a0+
  (1/2)*(al-bt)*bt*(am1+a1);
vector m610=(al-bt)*s+(lmf*(1-al)+bt*(al-bt-1))*a1+
  (1/2)*(al-bt)*bt*(a0+a2);
vector m710=(al-bt)*s+(lm*(1-al)+bt*(al-bt-1))*a2+
  (1/2)*(al-bt)*bt*(a1+a3); 
vector m310=(al-bt)*s+(lm*(1-al)+bt*(al-bt-1))*am2+
  (1/2)*(al-bt)*bt*(am1+am3); 
  vector m810=(al-bt)*s+(lmf*(1-al)+bt*(al-bt-1))*a3+
  (1/2)*(al-bt)*bt*(a2+a4);    
  vector m210=(al-bt)*s+(lmf*(1-al)+bt*(al-bt-1))*am3+
  (1/2)*(al-bt)*bt*(am2+am4);    
  
  
vector m511=(al-bt)*s2+(lm2*(1-al)+bt*(al-bt-1))*a0+
  (1/2)*(al-bt)*bt*(am2+a2);
vector m612=(al-bt)*s2f+(lm2f*(1-al)+bt*(al-bt-1))*a1+
  (1/2)*(al-bt)*bt*(a3+am1); 
vector m412=(al-bt)*s2f+(lm2f*(1-al)+bt*(al-bt-1))*am1+
  (1/2)*(al-bt)*bt*(am3+a1);   
  
  
vector m513=(al-bt)*s3+(lm3*(1-al)+bt*(al-bt-1))*a0+
  (1/2)*(al-bt)*bt*(am3+a3);
  
vector m614=(al-bt)*s3f+(lm3f*(1-al)+bt*(al-bt-1))*a1+
  (1/2)*(al-bt)*bt*(a4+am2);  
vector m415=(al-bt)*s3t+(lm3f*(1-al)+bt*(al-bt-1))*am1+
  (1/2)*(al-bt)*bt*(am4+a2);

      
  

Mult[1][2]=m12; Mult[1][3]=m13; Mult[1][4]=m14; 
Mult[2][3]=m23; Mult[2][4]=m24; Mult[2][5]=m25; 
Mult[3][4]=m34; Mult[3][5]=m35; Mult[3][6]=m36; 
Mult[4][5]=m45; Mult[4][6]=m46; Mult[4][7]=m47; 
Mult[2][1]=m12; Mult[3][1]=m13; Mult[4][1]=m14;
Mult[3][2]=m23; Mult[4][2]=m24; Mult[5][2]=m25; 
Mult[4][3]=m34; Mult[5][3]=m35; Mult[6][3]=m36; 
Mult[5][4]=m45; Mult[6][4]=m46; Mult[7][4]=m47; 

Mult[5][6]=m56; Mult[5][7]=m57; Mult[6][7]=m67; Mult[5][8]=m58; Mult[7][8]=m78;
Mult[6][5]=m56; Mult[7][5]=m57; Mult[7][6]=m67; Mult[8][5]=m58; Mult[8][7]=m78;
 Mult[7][9]=m79; Mult[8][9]=m89;
  Mult[9][7]=m79; Mult[9][8]=m89;


Mult[3][10]=m310; Mult[4][10]=m410; Mult[5][10]=m510; Mult[6][10]=m610;
Mult[10][3]=m310; Mult[10][4]=m410; Mult[10][5]=m510; Mult[10][6]=m610;

Mult[7][10]=m710; Mult[8][10]=m810;
Mult[10][7]=m710; Mult[10][8]=m810;  

Mult[5][11]=m511; Mult[11][5]=m511;
Mult[4][12]=m412; Mult[12][4]=m412;
Mult[6][12]=m612; Mult[12][6]=m612;

Mult[5][13]=m513; Mult[13][5]=m513;

 
proc Times (vector u, vector v)
{
vector ans=[0];
list rem=list();
 for(int i=1; i<=15; i=i+1)
  { if (u[i]<>0)
     {
        for(int j=1; j<=15; j=j+1)
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

proc tau0 (vector v)
  {
return(v[9]*am4+v[8]*am3+v[7]*am2+v[6]*am1+v[5]*a0+v[4]*a1+v[3]*a2+v[2]*a3+v[1]*a4+v[10]*s+v[11]*s2+v[12]*s2f+v[13]*s3+v[14]*s3t+v[15]*s3f);        
  }  
  
  proc tau1(vector v)
{
if (v[1]==0 and v[2]==0)
{
return(v[3]*a4+v[4]*a3+v[5]*a2+v[6]*a1+v[7]*a0+v[8]*am1+v[9]*am2+v[10]*s+v[11]*s2+v[12]*s2f+v[13]*s3t+v[14]*s3f+v[15]*s3);}
else
{return("fail")}
}
 
proc fold (vector v)
{     
vector h=v[9]*am3+v[8]*am2+v[7]*am1+v[6]*a0+v[5]*a1+v[4]*a2+v[3]*a3+v[2]*a4+v[10]*s+v[12]*s2+v[11]*s2f+v[13]*s3f+v[14]*s3+v[15]*s3t;
        return(h);
                  } 
          
proc lambda (vector v)
{
if ( v[1]==0 and v[12]==0 and v[9]==0) 
  { poly p= lm3*v[2]+lm2*v[3]+lm*v[4]+v[5]+lm*v[6]+lm2*v[7]+lm3*v[8]+(lm-bt-bt*lm)*v[10]+(lm2-bt-bt*lm2)*v[11]+(lm3-bt-bt*lm3)*v[13]+(lm3f-bt-bt*lm3f)*v[14]+(lm3t-bt-bt*lm3t)*v[15];
  return(p); }
  else {return ("fail")}
}        

// define some eigenvectors 
vector u1=-s+(lm-bt-al*lm)*a0+((al-bt)/2)*(a1+am1);  // 0-eigenvector for a0
vector v1=s+(bt-lm)*a0+bt*(a1+am1)/2;   // al-eigenvector for a
vector u1u1=Times(u1, u1)[1];  // the product u1*u1 contains s*s with coefficient 1
vector u1v1=Times(u1, v1)[1]; // the product u1*v1 contains s*s with coefficient -1
vector v1v1=Times(v1, v1)[1]; //the product v1*v1 contains s*s with coefficient 1

u1u1+u1v1;  // this is a 0-eigenvector for a0

// calculate  lambda(s2f): lambda(u-u[12]*s2f)
vector w=(u1u1+u1v1)-(u1u1+u1v1)[12]*s2f;
 
poly ls2f=-lambda(w)/((u1u1+u1v1)[12]);
//(8*bt-2)/(3*bt)*lm^2+(-8*bt+2)/(3*bt)*lm*lmf+(-2*bt+1)*lm+(bt)*lm2+(-bt)

// update function lambda

proc lambda (vector v)
{
 if ( v[1]==0 and v[9]==0)
 {
 poly p= lm3*v[2]+lm2*v[3]+lm*v[4]+v[5]+lm*v[6]+lm2*v[7]+lm3*v[8]+(lm-bt-bt*lm)*v[10]+(lm2-bt-bt*lm2)*v[11]+ls2f*v[12]+(lm3-bt-bt*lm3)*v[13]+(lm3f-bt-bt*lm3f)*v[14]+(lm3t-bt-bt*lm3t)*v[15];
  return(p); 
  }
  else {return("fail")}
  }    

// compute lambda(s*s)
// u1*u1 is a 0-eigenvector for a0 and contains s*s with coefficient 1
// u1*u1=u1u1+s*s

poly ls2=-lambda(u1u1);

// express the product a0*s2f
// phi=u1*u1-v1*v1+lambda(v1*v1)*a0 is a0-eigenvector for a0

vector phi=u1u1-v1v1+ (lambda(v1v1)+ls2)*a0;

// Times(phi, a0)=0
Times(phi, a0); //  contains a0*s2f with nonzero coefficient 4*bt^2    

vector a0phi1=Times(phi, a0)[1];

vector m512=-Times(phi, a0)[1]/(4*bt^2);  //
Mult[5][12]=m512;
Mult[12][5]=m512;

//express s*s
vector psi=u1u1+u1v1;
vector ss=-Times(a0, psi)/al+Times(u1, v1)[1];

Mult[10][10]=ss;

// Equation (36) in Proposition 6.15
vector d=ss-fold(ss);
//(9*bt^2)/2*gen(12)+(-9*bt^2)/2*gen(11) : implies s2f=s2

// d is the zero vector, hence lambda(d) must be zero
lambda(d);
//  (6048*bt^4-6984*bt^3+2484*bt^2-270*bt+9)/128=9/128*(2*bt-1)*(12*bt-1)*(14*bt-1)

proc update(vector v)
{
return(v-v[12]*s2f+v[12]*s2);
}

// add some known products

Mult[6][11]=update(fold(m511)); // a1*s2
Mult[11][6]=update(fold(m511)); 

Mult[4][11]=update(tau0(Mult[6][11])); // am1*s2
Mult[11][4]=update(tau0(Mult[6][11]));

vector m311=tau0(fold(tau0( Times(a1,s2)))); // am2*s2
Mult[3][11]=m311;
Mult[11][3]=m311;

Mult[7][11]=tau0(m311); // a2*s2
Mult[11][7]=tau0(m311);

// Express s*s2
// more eigenvectors for a0 

vector u2=-s2+(lm2-bt-al*lm2)*a0+((al-bt)/2)*(a2+am2);  //  0-eigenvector for a0
vector v2=s2+(bt-lm2)*a0+bt*(a2+am2)/2;   //  al-eigenvector for a0

Times(u1, u2); // this is a 0-eigenvector for a0 and contains s*s2 with coefficient 1 
vector u1u2=Times(u1,u2)[1];

Times(v1, u2); // this is a al-eigenvector for a0 and contains s*s2 with coefficient -1 
vector v1u2=Times(v1, u2)[1];

Times(v1,v2); //. this contains s*s2 with coefficient 1 
vector v1v2=Times(v1,v2)[1];

vector p12=u1u2+v1u2;
 // in order to compute Times(a0, p12) we need the products a0*s3f e a0*s3t 

// compute lambda(s*s2)
// u1*u2 is a 0-eigenvector for a0, hence has lambda=0
poly lss2=-lambda(u1u2); 

vector phi12=u1u2-v1v2+ (lambda(v1v2)+lss2)*a0; // this is a 0-eigenvector for a0
Times(a0, phi12); // contains  the unknown products a0*s3f+a0*s3t with coeff 2*bt^2

// compute a0*(s3f+s3t)

vector a0s33=-Times(a0, phi12)[1]/(2*bt^2);

// now we can compute a0*p12
vector a0p12=Times(a0,p12)[1]+3*bt^2*a0s33;

// compute s*s2 using the relation: Times(a0, p12)=al*Times(v1, u2)=al*(Times(v1, u2)[1]-m1011); 

vector m1011=Times(v1, u2)[1]-a0p12/al;

Mult[10][11]=m1011;
Mult[11][10]=m1011;

// express s3f and s3t
// Times(s1,s2)-fold(times(s1,s2)) must be zero and it contains s3f with coefficient (15*bt^2)/4

vector S3f=update(-(Times(s,s2)-fold(Times(s,s2))-(15*bt^2)/4*s3f)/(15*bt^2)/4);
vector S3t=update(tau0(S3f));

proc update(vector v)
{
return(v-v[12]*s2f+v[12]*s2-v[15]*s3t+v[15]*S3t-v[14]*s3f+v[14]*S3f);
}

// express a4
// S3t-fold(S3t) must be zero and contains a4 wit coefficient (16*bt^2-10*bt+1)/(640*bt)

vector A4=update(-( S3t-fold(S3t) -(S3t-fold(S3t))[9]*a4)/(S3t-fold(S3t))[9]);

proc update(vector v)
{
return(v-v[12]*s2f+v[12]*s2-v[15]*s3t+v[15]*S3t-v[14]*s3f+v[14]*S3f-v[9]*a4+v[9]*A4);
}

 update((tau1(S3f)-S3f))[13];;   // -15/128

vector S3=-(update((tau1(S3f)-S3f))-update((tau1(S3f)-S3f))[13]*s3)/update((tau1(S3f)-S3f))[13];

proc update(vector v)
{
return(v-v[12]*s2f+v[12]*s2-v[15]*s3t+v[15]*S3t-v[14]*s3f+v[14]*S3f-v[9]*a4+v[9]*A4-v[13]*s3+v[13]*S3);
}

// update(update(S3f-fold(S3))) must be the zero vector and it contains am3 with non zero coefficient.
// hence we can express am3

update(update(S3f-fold(S3)))[2];   // (-48*bt^2+30*bt-3)/(512*bt)=-3(2*bt-1)(8*bt-1)/(512*bt)

vector Am3=-(update(update(S3f-fold(S3)))-update(update(S3f-fold(S3)))[2]*am3)/update(update(S3f-fold(S3)))[2];