//
// General Sakuma theorem: Case al=2bt, non symmetric
//
// (c) 2020 C. Franchi, M. Mainardis, S. Shpectorov
//
//
ring F=(0,bt),( lm, lmf, lm2, lm2f), dp;
freemodule(10);
vector am2=gen(1);
vector am1=gen(2);
vector a0=gen(3);
vector a1=gen(4);
vector a2=gen(5);
vector a3=gen(6);
vector s=gen(7);
vector s2=gen(8);
vector s2f=gen(9);
vector s3=gen(10);
list a=am2,am1,a0,a1,a2,a3,s,s2,s2f,s3;
poly al=2*bt;
list r=0,0,0,0,0,0,0,0,0,0;
list Mult=r,r,r,r,r,r,r,r,r,r;

int i;
for (i=1; i<=6; i++ ) {Mult[i][i]=a[i];}

vector m12=s+bt*(am2+am1);
vector m23=s+bt*(am1+a0);
vector m34=s+bt*(a0+a1);
vector m45=s+bt*(a1+a2);
vector m56=s+bt*(a2+a3);

vector m24=s2f+bt*(am1+a1);
vector m46=s2f+bt*(a1+a3);

vector m13=s2+bt*(am2+a0);
vector m35=s2+bt*(a0+a2);

vector m27=(al-bt)*s+(lmf*(1-al)+bt*(al-bt-1))*am1+
  (1/2)*(al-bt)*bt*(am2+a0);
vector m37=(al-bt)*s+(lm*(1-al)+bt*(al-bt-1))*a0+
  (1/2)*(al-bt)*bt*(am1+a1);
vector m47=(al-bt)*s+(lmf*(1-al)+bt*(al-bt-1))*a1+
  (1/2)*(al-bt)*bt*(a0+a2);
vector m38=(al-bt)*s2+(lm2*(1-al)+bt*(al-bt-1))*a0+
  (1/2)*(al-bt)*bt*(am2+a2);

Mult[1][2]=m12; Mult[1][3]=m13; Mult[2][3]=m23; Mult[2][4]=m24; Mult[3][4]=m34; Mult[3][5]=m35; Mult[4][5]=m45; Mult[4][6]=m46; 
Mult[2][1]=m12; Mult[3][1]=m13; Mult[3][2]=m23; Mult[4][2]=m24; Mult[4][3]=m34; Mult[5][3]=m35; Mult[5][4]=m45; Mult[6][4]=m46; 

Mult[5][6]=m56;  Mult[6][5]=m56; 

Mult[2][7]=m27; Mult[3][7]=m37; Mult[4][7]=m47; Mult[3][8]=m38;
Mult[7][2]=m27; Mult[7][3]=m37; Mult[7][4]=m47; Mult[8][3]=m38;

vector m36=s3+bt*(a0+a3);
Mult[3][6]=m36;
Mult[6][3]=m36;


 proc Times (vector u, vector v)
{
vector ans=[0];
list rem=list();
 for(int i=1; i<=10; i=i+1)
  { if (u[i]<>0)
     {
        for(int j=1; j<=10; j=j+1)
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

// Define the simmetries
  
  proc tau0 (vector v)
{
  if (v[6]==0) 
  {
return(v[5]*am2+v[4]*am1+v[3]*a0+v[2]*a1+v[1]*a2+v[7]*s+v[8]*s2+v[9]*s2f+v[10]*s3);        
  }  
  else  {return("fail");}
  }
  
  proc tau1(vector v)
{
 if (v[1]==0 and v[10]==0 ) 
   { vector u=v[2]*a3+v[3]*a2+v[4]*a1+v[5]*a0+v[6]*am1+v[7]*s
   +v[8]*s2+v[9]*s2f; 
   return(u);}
   else
   {return  ("fail")}
   }  
   
 
map ff=F, lmf,lm, lm2f, lm2;

proc fold (vector v)
{
poly v1=v[1];
poly v5=v[5];
poly v4=v[4];
poly v3=v[3];
poly v2=v[2];
poly v6=v[6];
poly v7=v[7];
poly v8=v[8];
poly v9=v[9];
poly v10=v[10];

if (v[10]==0)
       {vector h=ff(v6)*am2+ff(v5)*am1+ff(v4)*a0+ff(v3)*a1+ff(v2)*a2+ff(v1)*a3+ff(v7)*s+ff(v9)*s2+ff(v8)*s2f;
        return(h);}
        else
          {return("fail");}
          } 
          
proc lambda (vector v)
{
 if (v[6]==0 and v[9]==0 and v[10]==0) 
  { poly p= lm2*v[1]+lm*v[2]+v[3]+lm*v[4]+lm2*v[5]+(lm-bt-bt*lm)*v[7]+(lm2-bt-bt*lm2)*v[8];
  return(p); }
  else {return ("fail")}
}        

// define eigenvectors for a0

vector u1=(-s+(lm-bt-al*lm)*a0+((al-bt)/2)*(a1+am1))/al;  
vector v1=(s+(bt-lm)*a0+bt*(a1+am1)/2)/al;   
vector uu=Times(u1, u1)[1];  
vector uv=Times(u1, v1)[1]; 
vector vv=Times(v1, v1)[1]; 

vector w=(uu+uv)-(uu+uv)[9]*s2f;

// vector uu+uv is the sum of a 0- and a al-eigenvector and so it has lambda equal 0
// it contains s2f with coefficient  (uu+uv)[9], hence we obtain lambda(s2f)
poly ls2f=-lambda(w)/((uu+uv)[9]);

// update lambda

proc lambda (vector v)
{
 if (v[6]==0 and v[10]==0 ) 
  { poly p= lm2*v[1]+lm*v[2]+v[3]+lm*v[4]+lm2*v[5]+(lm-bt-bt*lm)*v[7]+(lm2-bt-bt*lm2)*v[8]+ls2f*v[9];
  return(p); }
  else {return ("fail")}
} 

// obtain lambda(s^2) from the 0-eigenvector u1*u1 
poly ls2=-4*(bt^2)*lambda(uu);

// apply the ressurection principle: phi is a 0-eigenvector for a0
vector phi=uu-vv- lambda(uu-vv)*a0;

// a0*phi must be zero. Since a0*phi contains s2 with non-zero coefficient, we get an expression for s2 and, applying fold, for s2f

vector a0phi=Times(phi, a0);
vector S2=2*a0phi/bt+s2; 
vector S2f=fold(S2); 

// update the multiplication with the new expressions for s2 and s2f
// update Mult[3][9] 
Mult[3][9]=Times(a0, S2f);;
Mult[9][3]=Mult[3][9];

// Function update: we substitute the vectors s2 and s2f with S2 and S2f.

proc update (vector v)
{
  return(v-v[8]*s2+v[8]*S2-v[9]*s2f+v[9]*S2f);
}

//vector m24=S2f+bt*(am1+a1);
//vector m46=S2f+bt*(a1+a3);

//vector m13=S2+bt*(am2+a0);
//vector m35=S2+bt*(a0+a2);

//vector m38=(al-bt)*S2+(lm2*(1-al)+bt*(al-bt-1))*a0+
//  (1/2)*(al-bt)*bt*(am2+a2);
//Mult[3][8]=m38; Mult[8][3]=m38;  

  
//vector a0s2f=update(Times(a0, S2f));

//
// Express a4 and am3
//
// tau1(S2)-S2=0 and this contains -bt*a4/2

vector A4=2*(tau1(S2+bt*am2/2)-S2)/bt;;
vector Am3=update(fold(A4));;

// Update tau0 and tau1

proc tau0 (vector v)
{
return(v[5]*am2+v[4]*am1+v[3]*a0+v[2]*a1+v[1]*a2+v[6]*Am3+v[7]*s+v[8]*S2+v[9]*S2f+v[10]*s3);        
  }  
  
  proc tau1(vector v)
{
 if (v[10]==0 ) 
   { vector u=v[1]*A4+v[2]*a3+v[3]*a2+v[4]*a1+v[5]*a0+v[6]*am1+v[7]*s
   +v[8]*S2+v[9]*S2f; 
   return(u);}
   else
   {return  ("fail")}
   }  
   
// Add products with s

Mult[1][7]=(al-bt)*s+(lm*(1-al)+bt*(al-bt-1))*a[1]+
  (1/2)*(al-bt)*bt*(Am3+a[2]);;
  Mult[7][1]=Mult[1][7];
Mult[6][7]=(al-bt)*s+(lmf*(1-al)+bt*(al-bt-1))*a[6]+
  (1/2)*(al-bt)*bt*(a[5]+A4);; 
  Mult[7][6]=Mult[6][7]; 
  Mult[5][7]=(al-bt)*s+(lm*(1-al)+bt*(al-bt-1))*a[5]+
  (1/2)*(al-bt)*bt*(a[4]+a[6]);;
Mult[7][5]=Mult[5][7];

// Find lm3: z is a 0-eigenvector for a0
vector z=phi+2*(-2*bt+lm)*u1;;

// this can be multiplied with s1 and the result has lambda equal zero

vector zs=Times(z,s);;

// a3 appears in zs with coefficient -(bt^3)/4. 

poly lm3=4*lambda(zs+((bt^3)*a3)/4)/(bt^3);;

// update lambda

proc lambda (vector v)
{
 return(lm2*v[1]+lm*v[2]+v[3]+lm*v[4]+lm2*v[5]+lm3*v[6]+(lm-bt-bt*lm)*v[7]+(lm2-bt-bt*lm2)*v[8]+ls2f*v[9]+(lm3-bt-bt*lm3)*v[10]);
 } 

// Find s*s

vector s1s1=4*bt^2*(uv-Times(a0, uu+uv)/al);;
Mult[7][7]=update(s1s1);

// s3  has  coefficient (bt^2)/4 in  s1s1 . Since s1s1 is f invariant we can express s3f

vector s3f=(s1s1-fold(s1s1-s1s1[10]*s3))/s1s1[10];
vector s3t=tau0(s3f);

// update f and tau1
proc f (vector v)
{
poly v1=v[1];
poly v5=v[5];
poly v4=v[4];
poly v3=v[3];
poly v2=v[2];
poly v6=v[6];
poly v7=v[7];
poly v8=v[8];
poly v9=v[9];
poly v10=v[10];
return(ff(v6)*am2+ff(v5)*am1+ff(v4)*a0+ff(v3)*a1+ff(v2)*a2+ff(v1)*a3+ff(v7)*s+ff(v9)*S2+ff(v8)*S2f+ff(v10)*s3f);
} 

  proc tau1(vector v)
{
return(v[1]*A4+v[2]*a3+v[3]*a2+v[4]*a1+v[5]*a0+v[6]*am1+v[7]*s
   +v[8]*s2+v[9]*s2f+v[10]*s3t); 
     }   
// 
// Complete the multiplication table
//
Mult[1][4]=s3f+bt*(am2+a1);;  Mult[4][1]=Mult[1][4];
Mult[2][5]=s3t+bt*(am1+a2);;  Mult[5][2]=Mult[2][5];
Mult[2][6]=tau0(Times(a1,Am3));;  Mult[6][2]=Mult[2][6];
Mult[1][5]=f(Mult[2][6]);;  Mult[5][1]=Mult[1][5];
Mult[1][6]=tau0(Times(Am3,a2));;  Mult[6][1]=Mult[1][6];
Mult[1][8]=update(Times(am2, S2));;  Mult[8][1]=Mult[1][8];
Mult[1][9]=update(Times(am2, S2f));;  Mult[8][1]=Mult[1][8];
Mult[3][10]=(al-bt)*s3+(lm3*(1-al)+bt*(al-bt-1))*a0+(1/2)*(al-bt)*bt*(Am3+a3);;
Mult[10][3]=Mult[3][10];
Mult[4][10]=f(update(Times(a0, s3f)));;  Mult[10][4]=Mult[4][10];
Mult[5][10]=tau1(update(Times(a0, s3t)));;  Mult[10][5]=Mult[5][10];
Mult[1][10]=tau0(Mult[5][10]);;  Mult[10][1]=Mult[1][10];
Mult[2][10]=tau0(Mult[4][10]);;  Mult[10][2]=Mult[2][10];
Mult[6][10]=f(update(Times(am2, s3f)));;  Mult[10][6]=Mult[6][10];
Mult[6][8]=Times(a3, s2);; Mult[8][6]=Mult[6][8];
Mult[6][9]=Times(a3, s2f);; Mult[9][6]=Mult[6][9];

// Find s3*s3
// eigenvectors for a0 involving s3
vector u3=-s3+(lm3-al*lm3-bt)*a0+((al-bt)/2)*(a3+Am3);;  // 0-eigenvector
vector v3=s3+(bt-lm3)*a0+bt*(a3+Am3)/2;;   // al-eigenvector
vector u3u3=Times(u3, u3)[1];; 
vector u3v3=Times(u3, v3)[1];; 
vector v3v3=Times(v3, v3)[1];; 

// u3*v3 is an al-eigenvector, so it has lambda equal zero, and contains s3*s3 with 
// coefficient -1
poly ls3s3=lambda(u3v3[1]);;

vector psi3=u3u3+u3v3;;
vector s3s3=(-Times(a0, psi3)+al*u3v3)/al;;

Mult[10][10]=update(s3s3);;

vector u1u3=Times(u1, u3)[1];; // contains  s1*s3 with coefficient 1/(2*bt)
vector u1v3=Times(u1, v3)[1];; // contains  s1*s3 with coefficient -1/(2*bt)
vector C=u1u3+u1v3;;

vector s1s3=2*bt*(u1v3-Times(a0, C)/al);;
Mult[7][10]=update(s1s3);;
Mult[10][7]=Mult[7][10];


// Function lambdb: it is lambda_{a_1}
//   
proc lambdb (vector u) 
{ 
poly lu=lambda(f(u));
 return(ff(lu));
}

// Useful relations: vectors d1, d2, D1, D2, ee, g are zero
vector d1=f(s3t)-s3t;;     
vector d2=tau1(d1);;       
vector D1=tau0(d1)-d1;;  
vector D2=tau0(d2)-d2;;
vector e=update(Times(tau1(u1), tau1(v3)));
vector ee=update(Times(a2,e)-2*bt*e);

vector u2=-S2+(lm2-al*lm2-bt)*a0+((al-bt)/2)*(a2+am2);;  // 0-eigenvector for a0
vector g=update(Times(a0, update(Times(u1,u2))));

vector id4=Times(A4,A4)-A4;;
vector W= update(Times(a0, update(Times(u1,u1))));  

// polynomial relations
poly p1=lambda(id4);;  // poly4
poly p2=lambda(d1);;   // poly1
poly p3=lambda(d2);;  // poly2
poly p4=lambdb(d1);;  // poly6
poly p5=lambdb(update(g-f(g)));;

// polynomials Z and Zf
poly zz=2/(bt)*lm+(2*bt-1)/(bt^2)*lmf+(-4*bt+1)/(bt);
poly zzf=(2*bt-1)/(bt^2)*lm+2/(bt)*lmf+(-4*bt+1)/(bt);

// controlla questa parte 
// More relations
//
vector id3=Times(Am3,Am3)-Am3;;
poly poly3=lambda(id3);; 
vector id4=Times(A4,A4)-A4;;
poly poly4=lambda(id4);;  




vector W= update(Times(a0, update(Times(u1,u1))));    
poly poly7=lambda(W);

vector W1= update(Times(u1,am2-a2));    
poly poly8=lambda(W1);
// fine controllo 

// Classification
//
// 
proc val ( poly l, poly lf, poly l2, poly l2f, poly p)
{
map va=F, l,lf,l2,l2f;
return(va(p));
}

proc Val (poly l, poly lf, poly l2, poly l2f, vector  v) 
{
   return  (val(l,lf,l2,l2f,v[1])*am2+val(l,lf,l2,l2f,v[2])*am1+val(l,lf,l2,l2f,v[3])*a0+val(l,lf,l2,l2f,v[4])*a1+val(l,lf,l2,l2f,v[5])*a2+val(l,lf,l2,l2f,v[6])*a3+val(l,lf,l2,l2f,v[7])*s
   +val(l,lf,l2,l2f,v[10])*s3);        
   }  


//Case: ch F=7, bt=2,  lm2=lm2f=1
factorize(val(lm, lmf, 1,1,p1));
factorize(val(lm, lmf, 1,1,p2));
factorize(val(lm, lmf, 1,1,p3));
factorize(val(lm, lmf, 1,1,p4));
factorize(val(lm, lmf, 1,1,p5));

// Case: D_e=3, Ve=Vo=3C(2)
// 

val(-3/4*lmf+7/2, lmf, bt/2, bt/2, p1);
val(-3/4*lmf+7/2, lmf, bt/2, bt/2, p2);
val(-3/4*lmf+7/2, lmf, bt/2, bt/2, p3);
val(-3/4*lmf+7/2, lmf, bt/2, bt/2, p4);
val(-3/4*lmf+7/2, lmf, bt/2, bt/2, p5);

// if lmf=7
val(-3/4*7+7/2, 7, bt/2, bt/2, p4);
val(-3/4*7+7/2, 7, bt/2, bt/2, p5);

// if lmf=14/3
val(-3/4*14/3+7/2, 14/3, bt/2, bt/2, p4);
val(-3/4*14/3+7/2, 14/3, bt/2, bt/2, p5);

// Case: D_e=3, Ve=Vo=3A(2bt, bt) with 9*bt^2-10*bt+2=0, or bt=2/7
// 
// coefficient of s in d1:
Val(lm, lmf, (9*bt^2-2*bt)/(8*bt-2), (9*bt^2-2*bt)/(8*bt-2), update(d1))[7];

// we get lm= 2*bt*(1-bt) and lmf=bt*(2*bt+1)
// compute the difference between the coefficients of a0 and am2 in d1:
Val(2*bt*(1-bt), bt*(2*bt+1), (9*bt^2-2*bt)/(8*bt-2), (9*bt^2-2*bt)/(8*bt-2), update(d1))[3]-Val(2*bt*(1-bt), bt*(2*bt+1), (9*bt^2-2*bt)/(8*bt-2), (9*bt^2-2*bt)/(8*bt-2), update(d1))[1];

factorize(val(lm, lmf, 1,1,p1));

// System (32)
//
// Z(lm, lmf)=0 gives lm=(4*bt-1)/2-(2*bt-1)/(2*bt)*lmf
// second equation of system (32)
 poly eq2=4*val((4*bt-1)/2-(2*bt-1)/(2*bt)*lmf, lmf, 1,lm2f,zzf)*(lmf-bt)-2*lm2f;
 
 // third equation
 poly eq3=-8/bt*(lm-lmf)* ( 2*bt-lm-lmf)+2*(2*bt-1)^2/(bt^2)*(lmf-bt)-2*(1-lm2f);

val((4*bt-1)/2-(2*bt-1)/(2*bt)*lmf, lmf, 1,lm2f,p2);
val((4*bt-1)/2-(2*bt-1)/(2*bt)*lmf, lmf, 1,lm2f,p4);

// Case: lm2=0, bt=1/4
poly bt=1/4;
val((4*bt-1)/2-(2*bt-1)/(2*bt)*lmf, lmf, 1,0,eq3);
val(1/2, 1/2, 1,0,p2);
val(1/2, 1/2, 1,0,p4);

// Case: lm2=bt
 val((4*bt-1)/2-(2*bt-1)/(2*bt)*lmf, lmf, 1,bt,eq2)+
  val((4*bt-1)/2-(2*bt-1)/(2*bt)*lmf, lmf, 1,bt,eq3);
// get lmf=bt*(4*bt^2-3*bt+1)/(2*bt-1)^2;  
 val((4*bt-1)/2-(2*bt-1)/(2*bt)*bt*(4*bt^2-3*bt+1)/(2*bt-1)^2, bt*(4*bt^2-3*bt+1)/(2*bt-1)^2, 1,bt,eq2);
 
 
  val((4*bt-1)/2-(2*bt-1)/(2*bt)*bt*(4*bt^2-3*bt+1)/(2*bt-1)^2, bt*(4*bt^2-3*bt+1)/(2*bt-1)^2, 1,bt,eq3);  
   val((4*bt-1)/2-(2*bt-1)/(2*bt)*bt*(4*bt^2-3*bt+1)/(2*bt-1)^2, bt*(4*bt^2-3*bt+1)/(2*bt-1)^2, 1,bt,p2); 
     val((4*bt-1)/2-(2*bt-1)/(2*bt)*bt*(4*bt^2-3*bt+1)/(2*bt-1)^2, bt*(4*bt^2-3*bt+1)/(2*bt-1)^2, 1,bt,p4); 
     // (512*bt^11-1792*bt^10+2432*bt^9-960*bt^8-1104*bt^7+1600*bt^6-824*bt^5+108*bt^4+92*bt^3-54*bt^2+12*bt-1)/(256*bt^9-1024*bt^8+1792*bt^7-1792*bt^6+1120*bt^5-448*bt^4+112*bt^3-16*bt^2+bt)
  
//   
// systems in the proof of Theorem 1.1
// 
// search for solutions (lm, 2*bt-lm, bt,bt) such that (lm-bt)^2=bt^2/4
// in particular lm<>bt
//
val(lm, 2*bt-lm, bt,bt,p1); 
val(lm, 2*bt-lm, bt,bt,p2); 
val(lm, 2*bt-lm, bt,bt,p3); 
val(lm, 2*bt-lm, bt,bt,p4); 
val(lm, 2*bt-lm, bt,bt,p5); 

poly pp1=val(lm, 2*bt-lm, bt,bt,p1); 
// we see that the last four polynomials are multiple of (lm-bt)
// val(lm, 2*bt-lm, bt,bt,p2)=-2/(bt^4)*(lm-bt)*pp2
 poly pp2=(24*bt-20)*lm^3+(-60*bt^2+54*bt-4)*lm^2+(4*bt^4+38*bt^3-38*bt^2+6*bt)*lm+(2*bt^5-7*bt^4+7*bt^3-2*bt^2);
 
// val(lm, 2*bt-lm, bt,bt,p3)=-2/(bt^6)*(lm-bt)*pp3 
 poly pp3=(96*bt-64)*lm^4+(48*bt^3-416*bt^2+276*bt-8)*lm^3+(-108*bt^4+590*bt^3-400*bt^2+20*bt)*lm^2+(8*bt^6+48*bt^5-286*bt^4+214*bt^3-14*bt^2)*lm+(-2*bt^7+13*bt^6+12*bt^5-25*bt^4+2*bt^3);
 
 //  val(lm, 2*bt-lm, bt,bt,p4)=2/(bt^5)*(lm-bt)*pp4
 poly pp4=(24*bt^2-12*bt-4)*lm^3+(-92*bt^3+42*bt^2+16*bt)*lm^2+(4*bt^5+110*bt^4-44*bt^3-20*bt^2)*lm+(-10*bt^6-37*bt^5+11*bt^4+8*bt^3);

// val(lm, 2*bt-lm, bt,bt,p5)=1/(bt^5)*(lm-bt)*pp5
 poly pp5=(8*bt^2-8*bt+2)*lm^4+(24*bt^4-52*bt^3+52*bt^2-18*bt+2)*lm^3+(16*bt^6-80*bt^5+86*bt^4-95*bt^3+37*bt^2-6*bt)*lm^2+(-32*bt^7+56*bt^6-24*bt^5+49*bt^4-22*bt^3+5*bt^2)*lm+(8*bt^8+16*bt^7-16*bt^6-2*bt^5+3*bt^4-bt^3);
 
 // further condition on lm
 poly p=(lm-bt)^2-(bt^2)/4;
 
 // the polynomials p, ppi have a common root iff their resultant is zero
poly res1=resultant(p,pp1, lm); 
// (64*bt^12-576*bt^11+1968*bt^10-2848*bt^9+1132*bt^8+748*bt^7-1539*bt^6+2768*bt^5-1317*bt^4+140*bt^3-80*bt^2+8*bt+12)/(4*bt^8)
poly res2=resultant(p,pp2, lm);
// (32*bt^10-16*bt^9+8*bt^8-4*bt^7-4*bt^6+2*bt^5)
poly res3=resultant(p,pp3, lm); 
// (80*bt^14+672*bt^13-984*bt^12-424*bt^11+1261*bt^10-868*bt^9+323*bt^8-64*bt^7+4*bt^6)/4
poly res4=resultant(p,pp4, lm);
//(128*bt^12-32*bt^11+48*bt^10-48*bt^9+16*bt^8-10*bt^7+3*bt^6)/4
poly res5=resultant(p,pp5, lm);
// (1024*bt^16-7168*bt^15+3264*bt^14+11072*bt^13-17872*bt^12+12256*bt^11-5084*bt^10+1508*bt^9-339*bt^8+56*bt^7-4*bt^6)/64

// define the new ring F[bt]
// we look for common roots of res1, res2, res3, res4, res5, different from 0 and 1/2
ring F=(0), (bt), dp;
poly res1=(64*bt^12-576*bt^11+1968*bt^10-2848*bt^9+1132*bt^8+748*bt^7-1539*bt^6+2768*bt^5-1317*bt^4+140*bt^3-80*bt^2+8*bt+12)/(4*bt^8);
poly res2=(32*bt^10-16*bt^9+8*bt^8-4*bt^7-4*bt^6+2*bt^5);
poly res3=(80*bt^14+672*bt^13-984*bt^12-424*bt^11+1261*bt^10-868*bt^9+323*bt^8-64*bt^7+4*bt^6)/4;
poly res4=(128*bt^12-32*bt^11+48*bt^10-48*bt^9+16*bt^8-10*bt^7+3*bt^6)/4;
poly res5=(1024*bt^16-7168*bt^15+3264*bt^14+11072*bt^13-17872*bt^12+12256*bt^11-5084*bt^10+1508*bt^9-339*bt^8+56*bt^7-4*bt^6)/64;

//  we factorize res2: res2=2*bt^5*(2*bt-1)*(2*bt+1)*(2*bt^2+1)
factorize(res2);

// the solutions bt=0 and bt=1/2 are not allowed. Hence (2*bt+1)*(2*bt^2+1)=0
//
// If bt=-1/2: it cannot be a root of both res1 and res4
//
map vh=F, -1/2;

 vh(res1); // 781=11*71
  vh(res4); // 3/32

// 
// Assume  2*bt^2+1=0
ring F=(0, bt), (x), dp; 
minpoly=2*bt^2+1;
poly res1=(64*bt^12-576*bt^11+1968*bt^10-2848*bt^9+1132*bt^8+748*bt^7-1539*bt^6+2768*bt^5-1317*bt^4+140*bt^3-80*bt^2+8*bt+12)/(4*bt^8);
poly res2=(32*bt^10-16*bt^9+8*bt^8-4*bt^7-4*bt^6+2*bt^5);
poly res3=(80*bt^14+672*bt^13-984*bt^12-424*bt^11+1261*bt^10-868*bt^9+323*bt^8-64*bt^7+4*bt^6)/4;
poly res4=(128*bt^12-32*bt^11+48*bt^10-48*bt^9+16*bt^8-10*bt^7+3*bt^6)/4;
poly res5=(1024*bt^16-7168*bt^15+3264*bt^14+11072*bt^13-17872*bt^12+12256*bt^11-5084*bt^10+1508*bt^9-339*bt^8+56*bt^7-4*bt^6)/64;

// we see that res1,res3, res4 do not have common roots different from 0
res4; // (-3/16*bt+9/32) => bt=9/32*16/3=3/2
res1; // 1506*bt-597/2 =>1506*3/2-597/2=3921/2=3*1307/2;
res3; // -45/8*bt-1143/128 =>-45/8*3/2-1143/128=-2223/128=3^2*13*19/128

//
//// search for solutions (lm, lmf, bt,0) such that Z(lmf, lm)=0 Z(lm, lmf)(lm-bt)=bt/2
// Z(lmf, lm)=0 implies lmf=(4*bt-1)/2-(2*bt-1)/(2*bt)*lm
// by Equation (41) lm<>bt
//

// we see that p4=(-2*bt+1)/(bt^5)*(lm-bt)*[(4*bt-1)*lm-(5*bt^2-bt)]*(lm-bt^2)
factorize(val(lm, (4*bt-1)/2-(2*bt-1)/(2*bt)*lm, bt,0,p4));

// since lm<>bt, we have [(4*bt-1)*lm-(5*bt^2-bt)]*(lm-bt^2)=0

// 
// Assume lm=bt^2
//
val(bt^2, (4*bt-1)/2-(2*bt-1)/(2*bt)*bt^2, bt,0,zz*(bt^2-bt)-bt/2);
// (4*bt^3-10*bt^2+6*bt-1)/(2*bt)=(2*bt-1)*(2*bt^2-4*bt+1)/(2*bt)
// since bt is not 1/2, we get 2*bt^2-4*bt+1=0

ring F=(0, bt), (x), dp;
minpoly=2*bt^2-4*bt+1;


val(bt^2, (4*bt-1)/2-(2*bt-1)/(2*bt)*bt^2, bt,0,p1); 
//(6144*bt^13-58624*bt^12+249600*bt^11-627904*bt^10+1041832*bt^9-1204832*bt^8+999410*bt^7-601838*bt^6+262868*bt^5-82154*bt^4+17838*bt^3-2546*bt^2+214*bt-8)/(bt^7)=(-12*bt+6) whence either bt=1/2, a contradiction,  or ch F=3

val(bt^2, (4*bt-1)/2-(2*bt-1)/(2*bt)*bt^2, bt,0,p2); 
// (-96*bt^8+544*bt^7-1280*bt^6+1648*bt^5-1290*bt^4+630*bt^3-186*bt^2+30*bt-2)/(bt^3)=(-6*bt+2), gives a contradiction when ch F=3

// 
// Assume (4*bt-1)*lm-(5*bt^2-bt)=0, whence lm=(5*bt^2-bt)/(4*bt-1);
//
val((5*bt^2-bt)/(4*bt-1), (4*bt-1)/2-(2*bt-1)/(2*bt)*(5*bt^2-bt)/(4*bt-1), bt,0,p4); //0
val((5*bt^2-bt)/(4*bt-1), (4*bt-1)/2-(2*bt-1)/(2*bt)*(5*bt^2-bt)/(4*bt-1), bt,0, zz*(lm-bt)-bt/2);
// (-2*bt^2+bt)/(4*bt-1)=-bt*(2*bt-1)/(4*bt-1) it is zero only if bt=0,1/2 


//
// check that (3*bt/2, bt, bt, 0) is not a solution of the set T
val(3*bt/2, bt, bt,0,p2); // (16*bt^2-12*bt+2)=2*(2*bt-1)*(4*bt-1)

// it follows bt=1/4. 
val(3/8, 1/4, 1/4,0,p1); // 3







