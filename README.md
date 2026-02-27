Absolutely no AI was used in the creation of this project :)

# lobotomy

Lobotomy is a very simple programming language that compiles to Brainf*ck.

## Architecture

Compilation happens in four steps:
1. Pest generates a parse tree for the program.
2. The parse tree is transformed almost 1:1 into an AST.
3. The AST is transformed into a symbol table and a list of instructions that reference
   symbols in the table.
4. The list of instructions and symbol table are transformed into Brainf*ck.

Steps one and two are implemented already.

Currently

<!-- ## Variables

Variable names all start with "`#`". Variables do not need to be declared and are
all initialized to zero.

## Types

There is only one type in lobotomy: unsigned 8 bit integers. -->


Here's a hello world program:

```
#c = 'h';
print #c;
#c = 'e';
print #c;
#c = 'l';
print #c;
print #c
#c = 'o';
print #c;
// etc.
```

Here's a program that computes the nth Fibonacci number:

```
#n = 5;
#f_n_minus_two = 0;
#f_n_minus_one = 1;

#t1 = #n - 1; // Zero if #n == 1
#t2 = #n - 2; // Zero if #n == 2
if #t1 { #t3 = 1; };
if #t2 { #t3 = 1; };
if #t3 { // If n == 1 or n == 2
    #t3 = '!';
    print #t3;
}

#n -= 2;
while #n {
    #f_n = #f_n_minus_one + #f_n_minus_two;
    #n -= 1;
};
```