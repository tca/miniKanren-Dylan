Module: miniKanren
Synopsis: 
Author:
Copyright: 


define class <logic-var> (<object>)
 slot id :: <integer>, required-init-keyword: id:;
end;

define class <minikanren-state> (<object>)
  slot substitution, required-init-keyword: s:;
  slot counter :: <integer>, required-init-keyword: c:;
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

define function lookup (lv, substitution)
  case
    empty?(substitution) => #f;
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
      unit(pair(new-substitution, mk-state.counter));
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
                         c: c);
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

define function mplus (stream1, stream2)
  case
    empty?(stream1) => stream2;
    instance?(stream1, <function>) => method() mplus(stream2, stream1()) end;
    otherwise => pair(head(stream1), mplus(tail(stream1), stream2));
  end case;
end function mplus;

define function bind (stream, goal)
  case
    empty?(stream) => mzero;
    instance?(stream, <function>) => method() bind(stream(), goal) end;
    otherwise => mplus(goal(head(stream)), bind(tail(stream), goal));
  end case;
end function bind;
