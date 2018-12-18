

/* Question 1, Task 1 & Task 2:
    Check appendix proof under section Proofs.pdf -> Q1 Proof
*/
/* Question 1, Open Question
    The reason why this is a design mistake is because it can't be used to prove other methods or functions
    and can only be used in another method body. It would be better if it was a 'function' or a 'function method'.
    Also because it's a pure method (not mutating the input and always returning the same for the same input) it should
    not be a method.
*/
method Abs(x : int) returns (y : int) 
    // return value doesn't deviate from intended value
    ensures 0 <= x ==> y == x; 
    ensures x < 0 ==> y == -x;
      // return value is greater or equal to zero
    ensures 0 <= y; 
{
    if (x < 0) { 
        y := -x; 
    } else {
        y := x; 
    }
}
