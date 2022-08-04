Our type models the type of the language in an ingenious way. The model is direct except for pointers. It does not annotate the type of the pointee, and the type of the pointee is recorded in the value model of pointers. This trick solves the impredicative problem in recursive type because any recursive type in our target languages is via pointers. Any recursive types therefore are modelled predicatively and non-recursively.


