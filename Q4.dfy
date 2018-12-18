
/* Question 4, Task 1:
    Completed specification for 'ComputeFact'
 */
 // Helper function to check factorial
function fact(n: nat): nat
    requires n >= 1
    decreases n
{
    if n == 1 then 1 else n * fact(n - 1)
}

method ComputeFact(n : nat) returns (res : nat)
    requires n > 0;
    ensures res == fact(n);
{
    res := 1;
    var i := 2;
    while (i <= n)
        invariant res == fact(i - 1) && (i <= n + 1)
        decreases n - i
    {
        res := res * i;
        i := i + 1;
    }
 }

 /* Question 4, Task 2:
    Check appendix proof under section Proofs.pdf -> Q4 Proof
  */