method test (x: int , y: int ) returns (z: int )
{
   
 assume (x==y) ;
 z:=x-y;
 assert (z ==0) ;

// oricare ar fi x  == y => x-y == 0;
//{{x == y}}z := x − y{{z == 0}}
//x = 4 ,y = 3 => F


//daca x = 100 => x este == 100
//{{true}}x := 100{{x == 100}}
//x := 1 => F


//
//{{0 <= x < 100}}x := x + 1{{0 <= x <= 100}}
// x := -2 => F


// {{true}}x := 2 ∗ y{{y <= x}}
// y = -1 => F

// {{0 <= x}}x := x − 1{{0 <= x}}
// x = 0 => F


 }



function Fib (n: nat) : nat {
     if n < 2 then n else Fib(n - 2) + Fib(n - 1)
 }


method identic6(x: array<int>, n: int) returns (rez: bool)
    ensures rez == (forall i :: 0 <= i < n - 1 ==> x[i] == x[i + 1])
{
    var identical: bool := true;

    for i := 0 to n - 2 {
        if x[i] != x[i + 1] {
            identical := false;
            break;
        }
    }

    rez := identical;
}


method Triple1 (x: int ) returns (r: int)
 {
 var y := 2 * x;
 r := x + y;
 }

 
 method Main()
 {
    //t  = 30
    var t := Triple1 (10) ;
    //warning
   // var t := Triple2 (10) ;
    //warning
   // var t := Triple (10) ;
    
 }


//for 3*x == r is true for 3*x+1 is warning 
 method Triple2 (x: int ) returns (r: int)
 {
 var y := 2 * x;
 r := x + y;
 assert r == 3 * x+1;
 }


 method Triple (x: int ) returns (r: int)
 {
 var y := 2 * x;
 r := x + y;
 assert r == 3 * x;
 //assert r < 5;
 assert true ;
 }


 

method Caller()
{
  var result := Triple11(18);
  assert result < 100; // true  3 * 18 = 54 < 100
}

method Triple11(x: int) returns (r: int)
  ensures r == 3 * x
{
  var y := 2 * x;
  r := x + y; // r = 3 * x
}

method Triple22(x: int) returns (r: int)
  requires x % 2 == 0 // Preconditie
  ensures r == 3 * x
{
  var y := x / 2;
  r := 6 * y; // r = 3 * x
}


// sau x % 6 ==0
method Triple33(x: int) returns (r: int)
  requires x % 6 == 0
  ensures r == 3 * x
{
  var y := x / 2;
  r := 6 * y;
}

//x >=0 si x%2 == 0 
method Triple44(x: int) returns (r: int)
  requires x % 2 == 0 && x >= 0
  ensures r == 3 * x
{
  var y := x / 2;
  r := 6 * y;
}
