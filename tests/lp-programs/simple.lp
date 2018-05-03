{a;b;c;d}.
e :- d.
f :- a,b.
:- b,c.
:- c,f.
:- not b().
:- not f().

:- not d().