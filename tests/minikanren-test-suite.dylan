Module: minikanren-test-suite
Synopsis:
Author:
License:

define test simple ()
  let equal = run (1, q) eqeq(1, 2); end;
  check-equal("== constants", equal, #());
end;

define function appendo (l, s, out)
  conde
    { eqeq(#(), l); eqeq(s, out) };
    { fresh(a, d, res)
        eqeq(pair(a, d), l);
        eqeq(pair(a, res), out);
        appendo(d, s, res);
      end;
    }
  end;
end function appendo;

define variable test-left = #(1, 2, 3);
define variable test-right = #(4, 5, 6);
define variable test-whole = #(1, 2, 3, 4, 5, 6);

define function query-all-ground ()
  run* (q)
    appendo(test-left, test-right, test-whole);
    eqeq(q, #t);
  end;
end;

define function query-infer-right ()
  run* (r)
    appendo(test-left, r, test-whole);
  end;
end;

define function query-infer-left ()
  run* (l)
    appendo(l, test-right, test-whole);
  end;
end;

define function query-infer-whole ()
  run* (w)
    appendo(test-left, test-right, w);
  end;
end;

define function query-infer-left-right ()
  run* (q)
    fresh(l, r)
      eqeq(q, list(l, r));
      appendo(l, r, test-whole);
    end
  end;
end;

define test test-append ()
  check-equal("all ground", query-all-ground(), #(#t));
  check-equal("infer left", query-infer-right(), #(#(4, 5, 6)));
  check-equal("infer right", query-infer-left(), #(#(1, 2, 3)));
  check-equal("infer whole", query-infer-whole(), #(#(1, 2, 3, 4, 5, 6)));
  check-equal("infer left and right", query-infer-left-right(),
              #(#(#(), #(1, 2, 3, 4, 5, 6)),
                #(#(1), #(2, 3, 4, 5, 6)),
                #(#(1, 2), #(3, 4, 5, 6)),
                #(#(1, 2, 3), #(4, 5, 6)),
                #(#(1, 2, 3, 4), #(5, 6)),
                #(#(1, 2, 3, 4, 5), #(6)),
                #(#(1, 2, 3, 4, 5, 6), #())));
end;

define function test-occurs-check1 ()
  run* (q)
    fresh (y)
      conde
      { eqeq(y, list(1, 2, q));
        eqeq(q, list(1, 2, y)) };
      { eqeq(q, list(1, 2, q)) };
      end;
    end;
  end;
end;

define test test-occurs-check ()
  check-equal("occurs-check", test-occurs-check1(), #());
end;

define function membero (x, l)
  fresh (head, tail)
    eqeq(l, pair(head, tail));
    conde
      { eqeq(x, head) };
      { membero(x, tail) };
    end;
  end;
end;

define function membero-minus ()
  run* (q)
    fresh (x, y)
      eqeq(x, y);
      eqeq(y, q);
      membero(q, #(1, 2, 3, 4, 5));
      not-eqeq(x, 3);
    end;
  end;
end;

define test test-disequality ()
  check-equal("members-minus", membero-minus(), #(1, 2, 4, 5));
end;

define function membero-absento ()
  run* (q)
    fresh (x, y)
      absento(q, 3);
      membero(q, #(1, 2, 3, 4, 5));
    end;
  end;
end;

define test test-absento ()
  check-equal("members-absento", membero-absento(), #(1, 2, 4, 5));
end;

define benchmark lists1 ()
  run (100, q)
    fresh (x, y, z)
      eqeq(list(x, y), q);
      appendo(x, y, z);
    end;
  end;
end;

define function make-test-list (n, m)
  if (n <= 0)
    m;
  else
    make-test-list(n - 1, pair(n,m));
  end;
end;

define constant $test-list = make-test-list(250, #());

define benchmark lists2 ()
  run* (q)
    fresh (x, y)
      eqeq(q, list(x, y));
      appendo(x, y, $test-list);
    end;
  end;
end;

define function lookupo (x, env, out)
  fresh (y, val, env^)
    eqeq(pair(pair(y, val), env^), env);
    //symbolo(x); symbolo(y);
    conde
      { eqeq(x, y); eqeq(val, out) };
      { not-eqeq(x, y); lookupo(x, env^, out) };
    end;
  end;
end function lookupo;

define function unboundo (x, env)
  fresh ()
    //symbolo(x);
    conde
      { eqeq(#(), env) };
      { fresh(y, v, env^)
          eqeq(pair(pair(y, v), env^), env);
          not-eqeq(x, y);
          unboundo(x, env^);
        end; };
    end;
  end;
end function unboundo;

define function eval-expo (expr, env, out)
  conde
// variable
{ symbolo(expr); lookupo(expr, env, out) };
// quote
{ fresh (b)
    eqeq(list(quote:, out), expr);
    absento(closure:, out);
    unboundo(quote:, env);
  end };
// list
{ fresh(expr*)
    eqeq(pair(list:, expr*), expr);
    eval-exp*o(expr*, env, out);
    unboundo(list:, env);
  end };
// lambda
{ fresh(x, body)
    eqeq(list(lambda:, list(x), body), expr);
    eqeq(list(closure:, x, body, env), out);
    symbolo(x);
    unboundo(lambda:, env);
  end };
// application
{ fresh (e1, e2, val, x, body, env^)
    eqeq(list(e1, e2), expr);
    eval-expo(e1, env, list(closure:, x, body, env^));
    eval-expo(e2, env, val);
    eval-expo(body, pair(pair(x, val), env^), out)
  end };
//cons
{ fresh (e1, e2, v1, v2)
    eqeq(list(cons:, e1, e2), expr);
    eqeq(pair(v1, v2), out);
    unboundo(cons:, env);
    eval-expo(e1, env, v1);
    eval-expo(e2, env, v2);
  end };
{ fresh (e, v2)
    eqeq(list(car:, e), expr);
    unboundo(car:, env);
    eval-expo(e, env, pair(out, v2));
  end };
{ fresh (e, v1)
    eqeq(list(cdr:, e), expr);
    unboundo(cdr:, env);
    eval-expo(e, env, pair(v1, out));
  end };
{ fresh (e, v)
    eqeq(list(null?:, e), expr);
    conde
      { eqeq(#(), v); eqeq(#t, out) };
      { not-eqeq(#(), v); eqeq(#f, out) };
    end;
    unboundo(null?:, env);
    eval-expo(e, env, v)
  end };
{ fresh (t, c, a, b)
    eqeq(list(if:, t, c, a), expr);
    unboundo(if:, env);
    eval-expo(t, env, b);
    conde
      { eqeq(#f, b); eval-expo(a, env, out) };
      { not-eqeq(#f, b); eval-expo(c, env, out) };
    end;
  end };
  end;
end function eval-expo;

define function eval-exp*o (expr*, env, out)
  conde
    { eqeq(#(), expr*); eqeq(#(), out) };
    { fresh (a, d, res-a, res-d)
        eqeq(pair(a, d), expr*);
        eqeq(pair(res-a, res-d), out);
        eval-expo(a, env, res-a);
        eval-exp*o(d, env, res-d)
      end };
  end
end function eval-exp*o;

define function interp-lists-test ()
  let program = list(car:, list(list:, list(quote:, x:)));
  run* (q)
    eval-expo(program, #(), q);
  end;
end;

define function interp-apply-test ()
  let fn = list(lambda:, list(x:), x:);
  let program = list(fn, list(quote:, x:));
  run* (q)
    eval-expo(program, #(), q);
  end;
end;

define test relational-interpreter ()
  check-equal("(car (list 'x))", interp-lists-test(), #(x:));
  check-equal("((lambda (x) x) 'x)", interp-apply-test(), #(x:));
end;

define benchmark interp-reverse ()
  let foo = run (100, q)
    eval-expo(q, #(), x:);
  end;
end;

define benchmark quines ()
  let res = run (10, q)
    eval-expo(q, #(), q);
  end;
  // print(res, *standard-output*, pretty?: #t);
end;

define benchmark twine ()
  let res = run (1, q)
    fresh (a, b)
      eqeq(list(a, b), q);
      eval-expo(b, #(), a);
      eval-expo(a, #(), b);
    end;
  end;
  // print(res, *standard-output*, pretty?: #t);
end;

define suite minikanren-test-suite ()
  test simple;
  test test-append;
  test test-occurs-check;
  test test-disequality;
  test test-absento;
  benchmark lists1;
  benchmark lists2;
  test relational-interpreter;
  benchmark interp-reverse;
  benchmark quines;
  benchmark twine;
end;

begin
  let filename = locator-name(as(<file-locator>, application-name()));
  if (split(filename, ".")[0] = "minikanren-test-suite")
    run-test-application(minikanren-test-suite);
  end;
end;
