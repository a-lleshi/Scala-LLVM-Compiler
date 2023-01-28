
def zero(x) = 0;

def suc(x) = x + 1;

def pred(x) =
  if x == 0 then x else x - 1;

def add(x, y) =
  if x == 0 then y else suc(add(x - 1, y));

def mult(x, y) =
  if x == 0 then 0 else add(y, mult(x - 1, y));

def pow(x, y) =
  if y == 0 then 1 else mult(x, pow(x, y - 1));

def fib(n) = if n == 0 then 0 
             else if n == 1 then 1 
             else fib(n - 1) + fib(n - 2);

def fact(n) =
  if n == 0 then 1 else n * fact(n - 1);

def ack(m, n) = if m == 0 then n + 1
                else if n == 0 then ack(m - 1, 1)
                else ack(m - 1, ack(m, n - 1));

def stack_test(x) = x + 1 + 2 + 3 + 4 + 5;

def div(x, y) = x / y;   //integer division

def rem(x, y) = x % y;   //remainder

def gcd(a, b) =
  if b == 0 then a else gcd(b, a % b);

def is_prime_aux(n, i) = 
  if n % i == 0 then 0
  else if (i * i) <= n then is_prime_aux(n, i + 1)  
  else 1;

def is_prime(n) = if n == 2 then 1 else is_prime_aux(n, 2);

def primes(n) = 
  if n == 0 then 0
  else if is_prime(n) == 1 then (write n; primes(n - 1)) 
  else primes(n - 1);

def is_collatz(n) =
  if n == 1 then 1
  else if n % 2 == 0 then is_collatz(n / 2)
  else is_collatz(3 * n + 1);  

def collatz_aux(n, i) = 
  if i > n then 0
  else if is_collatz(i) == 1 then (write i; collatz_aux(n, i + 1)) 
  else collatz_aux(n, i + 1);

def collatz(n) = collatz_aux(n, 1);

def facT(n, acc) =
  if n == 0 then acc else facT(n - 1, n * acc);


//zero(3)
//suc(8)
//pred(7)
//write(add(3, 4))
//mult(4,5)
//pow(2, 3)
//fib(20)
//(write(fact(5)) ; fact(6))
//(write(1) ; 2)
//write(ack(3, 12))   // for tail-rec test
//stack_test(0)
//(write (div(11, 3)); rem(11, 3))
//gcd(54, 24)
//is_prime(2)
primes(1000)
//primes(1000000)
//collatz(4000)
//collatz(5000)
//facT(6, 1)

