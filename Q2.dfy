
/* Question 2, Task 1:
    Because the postcondition don't take into account of 'x' and 'y' is equal Dafny can't verify
    the method. The body checks if x < y if it's false it could be x > y or x == y.
 */

/* Question 2, Task 2:
    Check appendix proof under section Proofs.pdf -> Q2 Proof
 */

/* Question 2, Task 3:
  */
method Q2_t3(x : int, y : int) returns (big : int, small : int)
    requires x != y;
    ensures big > small;
{
    if (x > y)
        {big, small := x, y;}
    else
        {big, small := y, x;}
}

/* Question 2, Task 4:
  */
method Q2_t4(x : int, y : int) returns (big : int, small : int) 
  ensures big >= small;
{
    if (x > y)
        {big, small := x, y;}
    else
        {big, small := y, x;}
}

/* Question 2, Bonus:
    The only way this could be made is if the you rewrote the method to do other stuff then what it's currently
    ment to do (modify the value in other ways)
 */