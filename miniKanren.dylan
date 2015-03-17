Module: miniKanren
Synopsis: 
Author:
Copyright: 

define sealed class <logic-var> (<object>)
 slot id :: <integer>, required-init-keyword: id:;
end;
define sealed domain make(singleton(<logic-var>));
define sealed domain initialize(<logic-var>);

define method print-object(object :: <logic-var>, stream :: <stream>) => ()
  // format(stream, "<lvar %s>", object.id);
  format(stream, "_.%s", object.id);
end;

define sealed class <minikanren-state> (<object>)
  slot substitution :: <list>, required-init-keyword: s:;
  slot counter :: <integer>, required-init-keyword: c:;
end;
define sealed domain make(singleton(<minikanren-state>));
define sealed domain initialize(<minikanren-state>);

define method print-object(object :: <minikanren-state>, stream :: <stream>) => ()
  format(stream, "<mks s: %s, c: %s>", object.substitution, object.counter);
end;

define inline function make-lvar (id :: <integer>) => (lvar :: <logic-var>)
  make(<logic-var>, id: id);
end function make-lvar;

define inline function lvar? (obj) => (is-lvar? :: <boolean>)
  instance?(obj, <logic-var>); 
end function lvar?;

define inline function lvar=? (lvar1 :: <logic-var>, lvar2 :: <logic-var>)
  => (vars-equal? :: <boolean>)
  lvar1.id == lvar2.id;
end function lvar=?;

define function lookup (lv :: <logic-var>, substitution :: <list>)
  if (empty?(substitution))
    #f;
  else 
    let first :: <pair> = head(substitution);
    let var :: <logic-var> = head(first);
    case  
      lvar=?(lv, var) => tail(first);
      otherwise => lookup(lv, tail(substitution));
    end case;
  end if;
end function lookup;

define function occurs-check (x :: <logic-var>, v, s :: <list>) => (occurs? :: <boolean>)
  let v^ = walk(v, s);
  case
      lvar?(v^) => lvar=?(v^, x);
      pair?(v^) => begin 
                     let v^^ :: <pair> = v^;
                     (occurs-check(x, head(v^^), s)
                        | occurs-check(x, tail(v^^), s));
                   end;
      otherwise => #f;
  end case;
end function occurs-check;

define function extend-s (x :: <logic-var>, v, s :: <list>)
  => (new-s :: <maybe-substitution>)
  if (occurs-check(x, v, s))
    #f;
  else
    pair(pair(x, v), s);
  end if;
end function extend-s;

define function walk(u, substitution :: <list>) => (root-value)
  let pr = lvar?(u) & lookup(u, substitution);
  if (pr)
    walk(pr, substitution);
  else
    u;
  end if;
end function walk;

define function eqeq(u, v) => (stream :: <mk-stream>)
  method(mk-state :: <minikanren-state>)
    let new-substitution = unify(u, v, mk-state.substitution);
    if (new-substitution)
      unit(make(<minikanren-state>, s: new-substitution, c: mk-state.counter));
    else
      mzero;
    end if;
  end method;
end function eqeq;

define constant mzero = #();

define inline function unit (mk-state :: <minikanren-state>)
  pair(mk-state, mzero);
end function unit;

define inline function pair? (obj) => (is-pair? :: <boolean>)
  instance?(obj, <pair>) 
end function pair?;

define constant <maybe-substitution> = type-union(singleton(#f), <list>);

define inline function unify-pair (u :: <pair>, v :: <pair>, s :: <list>)
  => (result :: <maybe-substitution>)
  let s^ = unify(head(u), head(v), s);
  s^ & unify(tail(u), tail(v), s^);
end function unify-pair;

// will need to collect prefix for =/=; dylan doesn't have eq?
define function unify (u, v, s :: <list>)
  => (result  :: <maybe-substitution>)
  let u = walk(u, s);
  let v = walk(v, s);
  case
    lvar?(u) & lvar?(v) & lvar=?(u, v) => s;
    lvar?(u) => extend-s(u, v, s);
    lvar?(v) => extend-s(v, u, s);
    pair?(u) & pair?(v) => unify-pair(u, v, s);
    (u == v) => s;
    otherwise => #f;
  end case;
end function unify;

define function call/fresh (fn :: <function>) => (goal :: <goal>)
  method(mk-state :: <minikanren-state>)
    let c = mk-state.counter;
    let mk-state^ = make(<minikanren-state>,
                         s: mk-state.substitution,
                         c: c + 1);
    let goal = fn(make-lvar(c));
    goal(mk-state^);
  end method;
end function call/fresh;

define function disj (goal1 :: <goal>, goal2 :: <goal>)
  => (interleaved-goals :: <goal>)
  method(mk-state :: <minikanren-state>)
    mplus(goal1(mk-state), goal2(mk-state));
  end method;
end function disj;

define function conj (goal1 :: <goal>, goal2 :: <goal>)
  => (conjoined-goals :: <goal>)
  method(mk-state :: <minikanren-state>)
    bind(goal1(mk-state), goal2);
  end method;
end function conj;

define function mplus (stream1 :: <mk-stream>, stream2 :: <mk-stream>)
  => (interleaved-stream :: <mk-stream>)
  if (instance?(stream1, <function>))
    method() mplus(stream2, stream1()) end;
  else
    let stream1^ :: <list> = stream1;
    case
      (stream1^ == mzero) => stream2;
      otherwise => pair(head(stream1^), mplus(tail(stream1^), stream2));
    end case;
  end if;
end function mplus;

define function bind (stream :: <mk-stream>, goal)
  => (new-stream :: <mk-stream>)
  if (instance?(stream, <function>))
    method() bind(stream(), goal) end;
  else
    let stream^ :: <list> = stream;
    case
      (stream^ == mzero) => mzero;
      otherwise => mplus(goal(head(stream^)), bind(tail(stream^), goal));
    end case;
  end if;
end function bind;

define macro Zzz
  { Zzz(?goal:*) } =>
    { method (mk-state :: <minikanren-state>)
        method ()
          ?goal(mk-state);
        end method;
      end method; }
end macro Zzz;

define macro conj+
  { conj+(?goal:expression) } => { Zzz(?goal) }
  { conj+(?goal:expression, ?goals:*) } => { conj(Zzz(?goal), conj+(?goals)) }
end macro conj+;

define macro disj+
  { disj+(?goal:expression) } => { Zzz(?goal) }
  { disj+(?goal:expression, ?goals:*) } => { disj(Zzz(?goal), disj+(?goals)) }
end macro disj+;

define macro fresh
  { fresh () ?goals:* end } => { conj+(?goals) }
  { fresh (?lvar:name, ?lvars:*) ?goals:* end }
    => { call/fresh(method(?lvar :: <logic-var>)
                      fresh (?lvars) ?goals end;
                    end method) }
  goals:
   {} => {}
   { ?goal:*; ... } => { ?goal, ... }
end macro fresh;

define macro conde
  { conde ?clauses end } => { disj+(?clauses) }
    clauses:
    { } => { }
    { { ?clause }; ... } => { conj+(?clause), ... }
    clause:
    { } => { }
    { ?goal:expression; ... } => { ?goal, ... }
end macro conde;

define macro run
  { run (?n:expression, ?lvars:*) ?goals:* end } => 
    { map(reify-1st, take(?n, call/goal(fresh (?lvars) ?goals end))) }
end;

define macro run*
  { run*(?lvars:*) ?goals:* end } => 
    { map(reify-1st, take-all(call/goal(fresh (?lvars) ?goals end))) }
end;

define constant $empty-state = make(<minikanren-state>, s: #(), c:0);
define constant <mk-stream> = type-union(<function>, <list>);
define constant <goal> = <function>;

define function call/goal(g :: <goal>)
  g($empty-state);
end function call/goal;

define function pull(stream :: <mk-stream>) => (forced :: <list>)
  if (instance?(stream, <function>))
    pull(stream());
  else
    stream;
  end if;
end function pull;

define function take(n :: <integer>, stream :: <mk-stream>)
  if (zero?(n))
    #()
  else 
    let stream^ = pull(stream);
    if (empty?(stream^))
      #()
    else
      pair(head(stream^), take(n - 1, tail(stream^)));
    end if;
  end if;
end function take;

define function take-all(stream :: <mk-stream>)
  let stream^ = pull(stream);
  if (empty?(stream^))
    #()
  else
    pair(head(stream^), take-all(tail(stream^)));
  end if;
end function take-all;

define function reify-1st (mk-state :: <minikanren-state>)
  let v = walk*(make-lvar(0), mk-state.substitution);
  walk*(v, reify-s(v, #()));
end function reify-1st;

define function walk* (v, s :: <list>)
  let v^ = walk(v, s);
  case
    lvar?(v^) => v^;
    pair?(v^) => begin
                   let v^^ :: <pair> = v^;
                   pair(walk*(head(v^^), s),
                        walk*(tail(v^^), s));
                 end;
    otherwise => v^;
  end case;
end function walk*;

define function reify-s(v, s :: <list>)
  let v^ = walk(v, s);
  case
    lvar?(v^) => begin
                   let n = make-lvar(size(s));
                   pair(pair(v^, n), s);
                 end;
    pair?(v^) => begin
                   let v^^ :: <pair> = v^;
                   reify-s(tail(v^^), reify-s(head(v^^), s));
                 end;
    otherwise => s;
  end case;
end function reify-s;
