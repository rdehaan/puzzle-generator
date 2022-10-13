alt(I) :- alt(I,_).

alt(I,conjunction(B)) :- alt(I,literal_tuple(B)),
        alt(I,hold(L)) : alt(I,literal_tuple(B, L)), L > 0;
    not alt(I,hold(L)) : alt(I,literal_tuple(B,-L)), L > 0.

alt(I,body(normal(B))) :- alt(I,rule(_,normal(B))), alt(I,conjunction(B)).
alt(I,body(sum(B,G)))  :- alt(I,rule(_,sum(B,G))),
    #sum { W,L :     alt(I,hold(L)), alt(I,weighted_literal_tuple(B, L,W)),
                     L > 0 ;
           W,L : not alt(I,hold(L)), alt(I,weighted_literal_tuple(B,-L,W)),
                     L > 0 }
         >= G.

  alt(I,hold(A)) : alt(I,atom_tuple(H,A))   :-
      alt(I,rule(disjunction(H),B)), alt(I,body(B)).
{ alt(I,hold(A)) : alt(I,atom_tuple(H,A)) } :-
      alt(I,rule(     choice(H),B)), alt(I,body(B)).

#show.
#show alt(I,T) : alt(I,output(T,B)), alt(I,conjunction(B)), not alt(I,hide(T)).
