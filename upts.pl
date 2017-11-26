%% -*- mode: prolog; coding: utf-8 -*-

%% GNU Prolog défini `new_atom`, mais SWI Prolog l'appelle `gensym`.
genatom(X, A) :- predicate_property(new_atom(_,_), built_in) ->
                     new_atom(X, A);
                 gensym(X, A).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Description de la syntaxe des termes %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%% wf(+E)
%% Vérifie que E est une expression syntaxiquement correcte.
%% Cette règle est inutile en soit, elle ne set qu'à documenter la forme des
%% termes du langage μPTS.

%% D'abord les termes du langage interne.
wf(X) :- identifier(X); integer(X); float(X).       %Une variable ou un nombre.
wf(fun(X, T, E)) :- identifier(X), wf(T), wf(E).    %Une fonction.
wf(app(E1, E2)) :- wf(E1), wf(E2).                  %Un appel de fonction.
wf(pi(X, T1, T2)) :- identifier(X), wf(T1), wf(T2). %Le type d'une fonction.
wf(forall(X, T, B)) :- identifier(X), wf(T), wf(B). %Le type d'une fonction implicite.
wf(let(X, T, E1, E2)) :- identifier(X), wf(T), wf(E1), wf(E2). %Definition locale.

%% Puis les éléments additionnels acceptés dans le langage source.
wf(fun(X, B)) :- identifier(X), wf(B).
wf(let(X, E1, E2)) :- identifier(X), wf(E1), wf(E2).
wf(let(Decls, E)) :- wf_decls(Decls), wf(E).
wf((T1 -> T2)) :- wf(T1), wf(T2).
wf(forall(X, B)) :- (identifier(X); wf_ids(X)), wf(B).
wf((E : T)) :- wf(E), wf(T).
wf(E) :- E =.. [Head|Tail], identifier(Head), wf_exps(Tail).
wf(X) :- var(X).       %Une métavariable, utilisée pour l'inférence de type.

%% identifier(+X)
%% Vérifie que X est un identificateur valide.
identifier(X) :- atom(X),
                 \+ member(X, [fun, app, pi, forall, (->), (:), let, [], (.)]).

wf_exps([]).
wf_exps([E|Es]) :- wf(E), wf_exps(Es).
wf_ids([]).
wf_ids([X|Xs]) :- identifier(X), wf_ids(Xs).
wf_decls([]).
wf_decls([X = E|Decls]) :-
    wf_decls(Decls), wf(E),
    (X = (X1 : T) -> wf(T), X1 =.. Ids, wf_ids(Ids);
     X =.. [F|Args], identifier(F), wf_args(Args)).
wf_args([]).
wf_args([X:T|Args]) :- wf_args(Args), identifier(X), wf(T).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Manipulation du langage interne %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% Occasionnellement pendant l'inférence de types, il se peut qu'une
%% métavariable apparaisse dans un terme du langage interne.  Donc les
%% prédicats ci-dessous font souvent attention à tester le cas `var(MV)`
%% (accompagné d'un `cut`) pour veiller à ne pas instancier cette
%% métavariable par inadvertance, parce que cela mène sinon très vite à des
%% boucles sans fin difficiles à déboguer.

%% subst(+Env, +X, +V, +Ei, -Eo)
%% Remplace X par V dans Ei.  V et Ei sont des expressions du langage interne.
%% Les variables qui peuvent apparaître libres dans V (et peuvent aussi apparaître
%% dans Ei) doivent toutes être incluses dans l'environnement Env.
%% Cette fonction évite la capture de nom, e.g.
%%
%%     subst(Env, x, y, fun(y,int,x+y), R)
%%
%% ne doit pas renvoyer `R = fun(y,int,y+y)` mais `R = fun(y1,int,y+y1)`.
subst(_, _, _, MV, Eo) :-
    %% Si MV est un terme non-instancié (i.e. une métavariable), la substitution
    %% ne peut pas encore se faire.  Dans certains cas, on pourrait renvoyer
    %% app(fun(X,Y),V), mais en général c'est problématique.
    %% Donc on impose ici la contrainte que les metavars ne peuvent pas
    %% faire référence à X.
    %% Le faire vraiment correctement est plus difficile.
    var(MV), !, Eo = MV.
subst(_, X, V, X, V).
subst(_, _, _, E, E) :- identifier(E); integer(E).
subst(Env, X, V, fun(Y, Ti, Bi), fun(Y1, To, Bo)) :-
    subst(Env, X, V, Ti, To),
    (X = Y ->
         %% If X is equal to Y, X is shadowed, so no subst can take place.
         Y1 = Y, Bo = Bi;
     (member((Y : _), Env) ->
          %% If Y appears in Env, it can appear in V, so we need to
          %% rename it to avoid name capture.
          genatom(Y, Y1),
          subst([], Y, Y1, Bi, Bi1);
      Y1 = Y, Bi1 = Bi),
     %% Perform substitution on the body.
     subst(Env, X, V, Bi1, Bo)).
subst(Env, X, V, pi(Y, Ti, Bi), pi(Y1, To, Bo)) :-
    subst(Env, X, V, fun(Y, Ti, Bi), fun(Y1, To, Bo)).
subst(Env, X, V, forall(Y, Ti, Bi), forall(Y1, To, Bo)) :-
    subst(Env, X, V, fun(Y, Ti, Bi), fun(Y1, To, Bo)).
subst(Env, X, V, app(E1i, E2i), app(E1o, E2o)) :-
    subst(Env, X, V, E1i, E1o), subst(Env, X, V, E2i, E2o).


%% apply(+Env, +F, +Arg, -E)
%% Les règles d'évaluations primitives.  Env donne le types des variables
%% libres qui peuvent apparaître.
apply(Env, fun(X, _, B), Arg, E) :- \+ var(B), subst(Env, X, Arg, B, E).
apply(_,   app(+, N1), N2, N) :- integer(N1), integer(N2), N is N1 + N2.
apply(_,   app(-, N1), N2, N) :- integer(N1), integer(N2), N is N1 - N2.


%% normalize(+Env, +Ei, -Eo)
%% Applique toutes les réductions possibles sur Ei et tous ses sous-termes.
%% Utilisé pour tester si deux types sont équivalents.
normalize(_, MV, Eo) :- var(MV), !, Eo = MV.
normalize(_, V, V) :- (integer(V); float(V); identifier(V)).
normalize(Env, fun(X, T, B), fun(X, Tn, Bn)) :-
    normalize([X:T|Env], T, Tn), normalize([X:T|Env], B, Bn).
normalize(Env, pi(X, T, B), pi(X, Tn, Bn)) :-
    normalize([X:T|Env], T, Tn), normalize([X:T|Env], B, Bn).
normalize(Env, forall(X, T, B), forall(X, Tn, Bn)) :-
    normalize([X:T|Env], T, Tn), normalize([X:T|Env], B, Bn).
normalize(Env, app(E1, E2), En) :-
    normalize(Env, E1, E1n),
    normalize(Env, E2, E2n),
    (apply(Env, E1n, E2n, E) ->
         normalize(Env, E, En);
     En = app(E1n, E2n)).

%% equal(+Env, +T1, +T2)
%% Vérifie que deux expressions sont égales.
%% Utilisé pour vérifier l'égalité des types au niveau du langage interne, où
%% `forall` and `pi` sont équivalents.
equal(_, E, E).
equal(Env, forall(X1, T1, E1), E2) :- equal(Env, pi(X1, T1, E1), E2).
equal(Env, E2, forall(X1, T1, E1)) :- equal(Env, E2, pi(X1, T1, E1)).
equal(Env, fun(X1, T1, E1), fun(X2, T2, E2)) :-
    equal(Env, T1, T2),
    Env1 = [X1:T1|Env],
    (X1 = X2 ->
         E3 = E2;
     %% Si X1 et X2 sont différents, renomme X2 dans E2!
     subst(Env1, X2, X1, E2, E3)),
    equal(Env1, E1, E3).
equal(Env, pi(X1, T1, E1), pi(X2, T2, E2)) :-
    equal(Env, fun(X1, T1, E1), fun(X2, T2, E2)).
equal(Env, E1, E2) :-
    normalize(Env, E1, E1n),
    normalize(Env, E2, E2n),
    ((E1 = E1n, E2 = E2n) ->
         %% There was nothing to normalize :-(
         fail;
     equal(Env, E1n, E2n) -> true).
        

%% verify(+Env, +E, +T)
%% Vérifie que E a type T dans le contexte Env.
%% E est une expression du langage interne (i.e. déjà élaborée).
%% Elle ne devrait pas contenir de métavariables.
verify(Env, E, T) :-
    verify1(Env, E, T1) ->
        (equal(Env, T, T1) -> true;
         write(user_error, not_equal(T, T1)), nl(user_error), fail);
    write(user_error, verify_failure(E)), nl(user_error), fail.

%% verify1(+Env, +E, -T)
%% Calcule le type de E dans Env.
verify1(_, MV, _) :- var(MV), !, fail.
verify1(_, N, int) :- integer(N).
verify1(_, N, float) :- float(N).
verify1(Env, X, T) :-
    %% `member(X:T, Env)` risquerait de trouver dans Env un autre X que le
    %% plus proche, au cas où il y a plusieurs X dans l'environnement.
    atom(X), (member(X:T1, Env) -> T = T1; fail).
verify1(Env, fun(X, T1, E), forall(X, T1, T2)) :-
    verify(Env, T1, type),
	%%write(user_error, 'x devrait être ajouter').
    verify1([X:T1|Env], E, T2).
	
verify1(Env, app(F, A), T2) :-
    verify(Env, F, pi(X, T1, T3)),
    verify(Env, A, T1),
    subst(Env, X, A, T3, T2).
	
	
verify1(Env, pi(X, T1, T2), type) :-
    verify(Env, T1, type), verify([X:T1|Env], T2, type).
	
verify1(Env, forall(X, T1, T2), T) :- verify1(Env, pi(X, T1, T2), T).

verify1(Env, let(X, T, E1, E2), Tret) :-
    verify(Env, T, type),
    Env1 = [X:T|Env],
    verify(Env1, E1, T),
    verify1(Env1, E2, Tret).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Élaboration du langage source vers le langage interne %%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%% expand(+Ei, -Eo)
%% Remplace un élement de sucre syntaxique dans Ei, donnant Eo.
%% Ne renvoie jamais un Eo égal à Ei.
expand(MV, _) :- var(MV), !, fail.
expand((T1 -> T2), pi(X, T1, T2)) :- genatom('x_', X).
%% !!!À COMPLÉTER!!!
expand((T1->T2->T3), pi(X, T1, pi(Y, T2, T3))) :- 
                                             genatom('x_', X), genatom('y_', Y).
expand((T1->T2->T3->T4), pi(X, T1, pi(Y, T2, pi(Z, T3, T4)))) :- 
                          genatom('x_', X), genatom('y_', Y), genatom('z_', Z).

expand(forall([], F), Fo):- expand(F, Fo).
expand(forall([n | Ts], F), forall(n, int, Fo)) :- genatom('x_',X), expand(forall(Ts, F), Fo).
expand(forall([T | Ts], F), forall(T, type, Fo)) :- genatom('x_',X), expand(forall(Ts, F), Fo).

expand(forall(T, F), forall(T, type, Fo)) :- genatom('x_', X), expand(F, Fo).
expand(list(T,N), pi(T, type, pi(N, int, type))).


%% coerce(+Env, +E1, +T1, +T2, -E2)
%% Transforme l'expression E1 (qui a type T1) en une expression E2 de type T2.
coerce(Env, E, T1, T2, E) :-
    T1 = T2;
    normalize(Env, T1, T1n),
    normalize(Env, T2, T2n),
    T1n = T2n.        %T1 = T2: rien à faire!
%% !!!À COMPLÉTER!!!


%% infer(+Env, +Ei, -Eo, -T)
%% Élabore Ei (dans un contexte Env) en Eo et infère son type T.
infer(_, MV, MV, _) :- var(MV), !.            %Une expression encore inconnue.
infer(Env, Ei, Eo, T) :- expand(Ei, Ei1), infer(Env, Ei1, Eo, T).
infer(_, X, X, int) :- integer(X).
infer(_, X, X, float) :- float(X).
infer(Env, (Ei : T), Eo, T1) :- check(Env, T, type, T1), check(Env, Ei, T1, Eo). 
%% !!!À COMPLÉTER!!!

%% Règle de typage 

%% Règle 2: Inférence du type d'une fonction
%% 1)Vérifier que E1 est un type en l'élaborant
%% 2) Mettre x comme e1 dans le contexte, inférer le type de e2 en l'élaborant aussi
infer(Env, fun(X, E1, E2), fun(X, E1o, E2o), pi(X, E1, E3)) :- 
   check(Env, E1, type, E1o),
   infer([X:E1o|Env], E2, E2o, E3).  %%ajout de X:E1o (Y or N)

%% Règle 4: Inférence du type "type" à pi(), soit un type de fonction.
%% 1) Vérifier que e1 est un type en l'élaborant.
%% 2) Vérifier que e2 est un type en l'élaborant. (Mettre x dans le contexte)
infer(Env, pi(X, E1, E2), pi(X, E1o, E2o), type) :-
    check(Env, E1, type, E1o),
    check([X:E1o|Env], E2, type, E2o). %%ajout de X:E1o (Y|N)

%% Règle 4.1: lorsqu'on a un un type list, il faut aller l'expand. 	
infer(Env, pi(X, list(T, N), list(T1, N1)), pi(X, E1oo, E2oo), type):-
    expand(list(T,N), E1o),
    infer(Env, E1o, E1oo, type),
	expand(list(T1, N1), E2o),
    infer(Env, E2o, E2oo, type).


%% Règle 5: Inférence du type "type" à forall().
%% 1) Vérifier que e1 est un type en l'élaborant.
%% 2) Vérifier que e2 est un type en l'élaborant. (Mettre x dans le contexte)
infer(Env, forall(X, E1, E2), forall(X, E1o, E2o), type) :-
    check(Env, E1, type, E1o),
    check([X:E1o|Env], E2, type, E2o). %%ajout de X:E1o (Y|N)


%% Règle 6: Inférence du type d'un appel de fonction.
%% 1) Inférer le type de e1 comme un pi en l'élaborant 
%% 2) Vérifier que le type de e2 soit e4 en l'élaborant. (mettre x dans le contexte)
infer(Env, app(E1, E2), app(E1o, E2o), Eo) :-
    infer(Env, E1, E1o, pi(X, E4, E5)),
    check(Env, E2, E4, E2o),
	subst(Env, X, E2o, E5, Eo). %% Vraiment pas très sûre.

%%Règle 7: Inférence du type d'une déclaration.
%% 1) Vérifier que e1 soit un type
%% 2) Ajouter x:e1 dans le contexte, vérifier que e2 est comme type e1
%% 3) Ajouter x:e1 dans le contexte, inférer le type e3 comme e4.
infer(Env, let(X, E1, E2, E3), let(X, E1o, E2o, E3o), E4) :-
    check(Env, E1, type, E1o),
    check([X:E1o|Env], E2, E1o, E2o),    %%ajout de X:E1o (Y|N)
	infer([X:E1o|Env], E3, E3o, E4).     %%ajout de X:E1o (Y|N)

%%Règle 8: Inférence du type d'une déclaration sucrée.
%% Je vais assumer que x est déjà dans l'environnement.
%% Comme Expand ne prends pas l'environnement, ça sert à rien de l'envoyer à expand.
%% 1) Inférer le type de e2 comme e1 en l'élaborant.
%% 2) Inférer le type de e3 comme e4 en l'élaborant.
infer(Env, let(X, E2, E3), let(X, E1, E2o, E3o), E4):-
    infer(Env, E2, E2o, E1),
	%%check(Env, X, E1, Xo),    %% Juste pour être sûr 
    infer(Env, E3, E3o, E4).

%%Règle 9: Inférence du type d'une annotation de type explicite.
%% 1) Vérifier que e2 est bien un type.
%% 2) Vérifier que e1 est de type e2.
infer(Env, E1:E2, E1o:E2o, E2o):-
    check(Env, E2, type, E2o),
    check(Env, E1, E2, E1o).
	
	


%% check(+Env, +Ei, +T, -Eo)
%% Élabore Ei (dans un contexte Env) en Eo, en s'assurant que son type soit T.
check(_Env, MV, _, Eo) :-
    %% On ne fait pas l'effort de se souvenir du type des métavariables,
    %% donc on ne peut pas vérifier si elle a effectivement le type attendu.
    %% À la place, on accepte n'importe quel usage de métavariable, en
    %% espérant qu'elles sont utilisées correctement.  C'est généralement le
    %% cas de toute façon, et pour les cas restants on se repose sur le filet
    %% de sécurité qu'est `verify`.
    var(MV), !, Eo = MV.
check(Env, Ei, T, Eo) :- expand(Ei, Ei1), check(Env, Ei1, T, Eo). %% PREMIER ARRÊT POUR L'INITIATION DE L'ENV
%% !!!À COMPLÉTER!!!

%% Règles de typage:
	
%% Règle 3: Vérification du type d'une fonction sucrée
%% 1) Voir, si dans l'environnement, on sait quelle est le type de X et qu'il est bien e_1 
%% 2) Vu que ce n'est qu'un check on devrait connaître au complet les paramétres de pi(x, e_1, e_3)
%%    Alors, on check si e_2 est de type e_3 
%% 3) Vu comment Expand est fait ce sucre ne sera pas traiter par celui-ci
%% THÉORIQUEMENT, on aurait déjà mis X:E1 dans l'environnement plus haut dans l'arbre, donc je peux regarder et il devrait pas y avoir de problème.
check(Env, fun(X, E2), pi(X, E1, E3), fun(X, Eo1, Eo2)):-
    check(Env, X, E1, Eo1),
	check(Env, E2, E3, Eo2).
    
%%Règle 10: Vérifcation d'un type:
%% 1) Inférer le type de e1 dans e2.
%% 2) Normaliser e2 et e3 et voir si c'est équivalent.
check(Env, E1, E3, E1o):-
     infer(Env, E1, E1o, E2), %% APRÈS EXPAND, DEUXIÈME ARRÊT POUR L'INITIATION DE L'ENV ET FIN.
     normalize(Env, E2, E3).
	
%%Règle 11: Vérification d'un forall():
%%Je vais assumer pour l'instant que x est typé comme e2 dans l'env. 
%% 1) Vérfier que e1 est de type e3.
check(Env, E1, forall(X, E2, E3), Eo):-
    check([X:E2|Env], E1, E3, Eo).            %%ajout de X:E1o (Y|N)

%% Vérifier que X est dans l'environnement et bien de type X. 
%% Utilisé:
%%         - Régle 2: Elle permet de vérifier que E1 est bien un type. 
check([X:T|Envs], X, T, X).
check([_:_|Envs], X, T, Eo) :- check(Envs, X, T, Eo).


%% Finalement, cas par défaut:
check(Env, Ei, T, Eo) :-
    infer(Env, Ei, Eo1, T1),
    (coerce(Env, Eo1, T1, T, Eo) -> true).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Environnement initial et tests %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


elaborate_env(Env, [], Env).
elaborate_env(Env, [X:Ti|Envi], Envo) :-
    check(Env, Ti, type, To) ->
        (verify(Env, To, type) -> elaborate_env([X:To|Env], Envi, Envo));
    write(user_error, 'FAILED_TO_ELABORATE'(Ti)), nl(user_error), !, fail.


	
	
initenv(Env) :-
    elaborate_env(
        [type : type],
        [int :  type,
         float :  type,
         bool :  type,
         int_to_float : (int -> float),
         int_to_bool : (int -> bool),
         list : (type -> int -> type),
         (+) : (int -> int -> int),
         (-) : (int -> int -> int),
         (*) : (int -> int -> int),
         (/) : (float -> float -> float),
         (<) : (float -> float -> int),
         if : forall(t, (bool -> t -> t -> t)),
         nil :  forall(t, list(t, 0)),
         cons : forall([t,n], (t -> list(t, n) -> list(t, n + 1))) %%forall(t,type,forall(n,int,pi(x_Nz,t,pi(y_7,list(t,n),list(t,n+1)))))

							],
        Env).

%% Quelques expressions pour nos tests.
sample(1 + 2). %% app(app(+ 1) 2) -
sample(1 / 2).
sample(cons(13,nil)).
sample(cons(1.0, cons(2.0, nil))).
sample(let([fact(n:int) = if(n < 2, 1, n * fact(n - 1))],
           fact(44))).
sample(let([fact(n) : (int -> int) = if(n < 2, 1, n * fact(n - 1))],
           fact(45))).
sample(let([list1 : forall(a, (a -> list(a, 1))) = fun(x, cons(x, nil))],
           list1(42))).
sample(let([list1(x) : forall(a, (a -> list(a, 1))) = cons(x, nil)],
           list1(43))).
sample(let([pushn(n,l) : pi(n, _, (list(int,n) -> list(int,n+1))) = cons(n,l)],
           %% L'argument `n` ne peut être que 0, ici, et on peut l'inférer!
           pushn(_,nil))).

%% Roule le test sur une expression.
test_sample(Env, E) :-
    infer(Env, E, Eo, T) ->
        normalize(Env, T, T1),
        write(user_error, inferred(E, T1)), nl(user_error),
        write(user_error, verifying(Eo)), nl(user_error),
        (verify(Env, Eo, T) ->
             write(user_error, 'VERIFIED!!'), nl(user_error);
         write(user_error, 'FAILED_TO_VERIFY'(Eo)), nl(user_error));
    write(user_error, 'FAILED_TO_INFER'(E)), nl(user_error).

%% Roule le test sur chacune des expressions de `sample`.
test_samples :-
    initenv(Env), sample(E), test_sample(Env, E).
	
	
	
	
%% Rapport des modifications:
%% J'ai initié l'environnement en premier comme je l'avais fait dans le check, mais dans infer.
%% Ensuite, je me suis lancée dans les règles de typage dans infer/check sans trouver une bonne façon de les tester.
%% J'ai ommis les 3 dernières règles de coerce; je ne suis pas encore certaine.

%% Après avoir fini les 11 premières règles de typage, l'initialisation ne se faisait plus correctement.
%% À cause de: (1) check(Env, Ei, T, Eo) :- expand(Ei, Ei1), check(Env, Ei1, T, Eo).

%% J'ai eu par exemple int_to_bool qui devenait pi(dummy_ x, int, bool)  , ce qui ne faisait plus de sens avec ce que j'avais au départ.
%% Si on va dans expand, il y a 
%% Dans le code original: expand((T1 -> T2), pi(X, T1, T2)) :- genatom('dummy_', X).  
%% ( pour l'instant je l'ai changé pour quelque chose de plus court pour la command GNU prolog)
%% Ç'a été la preuve que mes règles fonctionnaient, car dans (1) le check(Env, Ei1, T, Eo) fonctionnait.

%% Ainsi, je me suis dis que c'était sans doute ce qu'il fallait que ça fasse. 
%% Soit qu'on aille dans expand rendre l'environnement immédiatement en langage "interne"
%% Avant d'inférer leur type et les placer dans la liste de l'environnement.

%% J'ai refait l'initialisation en passant par expand (C'est indiquer le chemin pour l'initialisation dans check).

%% Par contre, je suis incertaine pour le cons.
%% Dans les données, on dit que ça devrait être pi(t, type, pi(x, t, pi(n, int, pi(y, list(t, n), list(t, n+1))))). 
%% où list(t, n) = pi(t, type, pi(n, int, type)).
%% Dans le code à cause du forall, ça me donne: forall(t,type,forall(n,int,pi(x_Nz,t,pi(y_7,list(t,n),list(t,n+1))))) 
%% (Note, L'expand de list se fait dans infer )
%% La différence principale est dans forall (C'est pas supposé déranger), et dans l'ordre des variables (exemple, n, int arrive plus tôt dans le code que dans les données).
%% J'ai passé longtemps à chercher une alternative, mais je ne trouve rien d'aussi satisfaisant que cela.

%% Ce qui reste à faire:
%% - Commencer les tests   (Car ça me semble plus simple pour implanter tous les cas des différentes expressions du lambda calcul possible du langage).
%% - Implanter le restant du sucre et la fonction coerce.