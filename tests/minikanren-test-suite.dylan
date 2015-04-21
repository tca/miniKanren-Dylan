Module: minikanren-test-suite
Synopsis:
Author:
License:

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

define suite minikanren-test-suite ()
  test test-append;
  test test-disequality;
  test test-absento;
  benchmark lists1;
  benchmark lists2;
end;

begin
  let filename = locator-name(as(<file-locator>, application-name()));
  if (split(filename, ".")[0] = "minikanren-test-suite")
    run-test-application(minikanren-test-suite);
  end;
end;
