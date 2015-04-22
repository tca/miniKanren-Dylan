Module: dylan-user

define library minikanren-test-suite
  use common-dylan;
  use io;
  use miniKanren;
  use system,
    import: { locators };
  use testworks;
end library minikanren-test-suite;

define module minikanren-test-suite
  use common-dylan;
  use standard-io;
  use print;
  use miniKanren;
  use locators,
    import: { <file-locator>,
              locator-name };
  use testworks;
end module minikanren-test-suite;
