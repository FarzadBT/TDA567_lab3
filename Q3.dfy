
/* Question 3, Task 1:
    n0 and m0 aren't mutable so they can't be changed
 */

/* Question 3, Task 2:
    This method is an implementation of multiplication.
    The needed specification for this are the 'ensure' and the two invariants.
    This is tested in the 'Main' below.
*/
method Q3(n0 : int, m0 : int) returns (res : int)
    ensures n0 * m0 == res;
{
    var n, m : int;
    res := 0;
    if (n0 >= 0) 
        {n,m := n0, m0;} 
    else 
        {n,m := -n0, -m0;}
    while (0 < n)
        invariant 0 <= n 
        invariant n0 >= 0 ==> (n0 - n) * m == res;
        invariant n0 < 0 ==> (-n0 - n) * m == res;
        decreases n
  { 
        res := res + m; 
        n := n - 1; 
    }
}

method Main() {
    // Simple 2 * 5 test
    var r := Q3(2, 5);
    assert r == 10;

    // Loop 0 -> 100 and multiply with itself
    var i := 0;
    while i < 100
        decreases  100 - i
    {
        r := Q3(i, i);
        assert r == (i * i);
        i := i + 1;
    }
}

/* Question 3, Task 3:
    Check appendix proof under section Proofs.pdf -> Q3 Proof
 */