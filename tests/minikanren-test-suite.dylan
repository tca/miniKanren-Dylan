Module: minikanren-test-suite
Synopsis:
Author:
License:

define function main ()
  let filename = locator-name(as(<file-locator>, application-name()));
  if (split(filename, ".")[0] = "minikanren-test-suite")
    run-test-application(minikanren-test-suite);
  end;
end function main;

define suite minikanren-test-suite ()
  test test-append;
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
