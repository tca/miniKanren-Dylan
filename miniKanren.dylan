Module: miniKanren
Synopsis: 
Author:
Copyright: 


define class <logic-var> (<object>)
 slot id :: <integer>, required-init-keyword: id:;
end;

define method print-object(object :: <logic-var>, stream :: <stream>) => ()
  // format(stream, "<lvar %s>", object.id);
  format(stream, "_.%s", object.id);
end;

define class <minikanren-state> (<object>)
  slot substitution, required-init-keyword: s:;
  slot counter :: <integer>, required-init-keyword: c:;
end;

define method print-object(object :: <minikanren-state>, stream :: <stream>) => ()
  format(stream, "<mks s: %s, c: %s>", object.substitution, object.counter);
end;

define function make-lvar (id :: <integer>)
  make(<logic-var>, id: id);
end function make-lvar;
  
define function lvar? (obj)
  instance?(obj, <logic-var>); 
end function lvar?;

define function lvar=? (lvar1 :: <logic-var>, lvar2 :: <logic-var>)
  lvar1.id = lvar2.id;
end function lvar=?;


define function null?(object)
  object == #();
end;

define function lookup (lv, substitution)
  case
    null?(substitution) => #f;
    lvar=?(lv, head(head(substitution))) => tail(head(substitution));
    otherwise => lookup(lv, tail(substitution));
  end case;
end function lookup;

define function extend-s (x, v, s)
  pair(pair(x, v), s);
end function extend-s;

define function walk(u, substitution)
  let pr = lvar?(u) & lookup(u, substitution);
  if (pr)
    walk(pr, substitution);
  else
    u
  end if;
end function walk;

define function eqeq(u, v)
  method(mk-state)
    let new-substitution = unify(u, v, mk-state.substitution);
    if (new-substitution)
      unit(make(<minikanren-state>, s: new-substitution, c: mk-state.counter));
    else
      mzero;
    end if;
  end method;
end function eqeq;

define variable mzero = #();

define function unit (mk-state)
  pair(mk-state, mzero);
end function unit;

define function pair? (obj)
  instance?(obj, <pair>) 
end function pair?;

define function unify-pair (u, v, s)
  let s^ = unify(head(u), head(v), s);
  s^ & unify(tail(u), tail(v), s^);
end function unify-pair;

// will need to collect prefix for =/=; dylan doesn't have eq?
define function unify (u, v, s)
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

define function call/fresh (fn)
  method(mk-state)
    let c = mk-state.counter;
    let mk-state^ = make(<minikanren-state>,
                         s: mk-state.substitution,
                         c: c + 1);
    let goal = fn(make-lvar(c));
    goal(mk-state^);
  end method;
end function call/fresh;

define function disj (goal1, goal2)
  method(mk-state)
    mplus(goal1(mk-state), goal2(mk-state));
  end method;
end function disj;

define function conj (goal1, goal2)
  method(mk-state)
    bind(goal1(mk-state), goal2);
  end method;
end function conj;

define function mplus (stream1, stream2) => (interleaved-stream)
  case
    null?(stream1) => stream2;
    instance?(stream1, <function>) => method() mplus(stream2, stream1()) end;
    otherwise => pair(head(stream1), mplus(tail(stream1), stream2));
  end case;
end function mplus;

define function bind (stream, goal)
  case
    null?(stream) => mzero;
    instance?(stream, <function>) => method() bind(stream(), goal) end;
    otherwise => mplus(goal(head(stream)), bind(tail(stream), goal));
  end case;
end function bind;

define macro Zzz
  { Zzz(?goal:*) } =>
    { method (mk-state)
        method ()
          ?goal(mk-state);
        end method;
      end method; }
end macro Zzz;

define macro conj+
  { conj+(?goal:expression) } => { Zzz(?goal) }
  { conj+(?goal:expression, ?goals:*) }=> { conj(Zzz(?goal), conj+(?goals)) }
end macro conj+;

define macro disj+
  { disj+(?goal:expression) } => { Zzz(?goal) }
  { disj+(?goal:expression, ?goals:*) }=> { disj(Zzz(?goal), disj+(?goals)) }
end macro disj+;

define macro fresh
  { fresh () ?goals:* end } => { conj+(?goals) }
  { fresh (?lvar:name, ?lvars:*) ?goals:* end }
    => { call/fresh(method(?lvar)
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
  { run(n, ?lvars:*) ?goals:* end } => 
    { map(reify-1st, take(n, call/goal(fresh (?lvars) ?goals end))) }
end;

define macro run*
  { run*(?lvars:*) ?goals:* end } => 
    { map(reify-1st, take-all(call/goal(fresh (?lvars) ?goals end))) }
end;

define variable empty-state = make(<minikanren-state>, s: #(), c:0);

define function call/goal(g)
  g(empty-state);
end function call/goal;

define function pull(stream)
  if (instance?(stream, <function>))
    pull(stream());
  else
    stream;
  end if;
end function pull;

define function take(n, stream)
  if (n = 0)
    #()
  else 
    let stream^ = pull(stream);
    if (null?(stream^))
      #()
    else
      pair(head(stream^), take(n - 1, tail(stream^)));
    end if;
  end if;
end function take;


define function take-all(stream)
  let stream^ = pull(stream);
  if (null?(stream^))
    #()
  else
    pair(head(stream^), take-all(tail(stream^)));
  end if;
end function take-all;

define function reify-1st (mk-state)
  let v = walk*(make-lvar(0), mk-state.substitution);
  walk*(v, reify-s(v, #()));
end function reify-1st;

define function walk* (v, s)
  let v^ = walk(v, s);
  case
    lvar?(v^) => v^;
    pair?(v^) => pair(walk*(head(v^), s),
                      walk*(tail(v^), s));
    otherwise => v^;
  end case;
end function walk*;

define function reify-s(v, s)
  let v^ = walk(v, s);
  case
    lvar?(v^) => block ()
                   let n = make-lvar(size(s));
                   pair(pair(v^, n), s);
                 end block;
    pair?(v^) => reify-s(tail(v^), reify-s(head(v^), s));
    otherwise => s;
  end case;
end function reify-s;
