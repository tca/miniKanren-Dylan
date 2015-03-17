Module: dylan-user

define library miniKanren
  use common-dylan;
  use io;
end library miniKanren;

define module miniKanren
  use common-dylan;
  use format;
  use format-out;
  use print;
  export
    eqeq, conj, disj,
    conde, fresh, run, run*
end module miniKanren;
