Module: dylan-user

define library miniKanren
  use common-dylan;
  use io;
end library miniKanren;

define module llrb-tree
  use common-dylan;
  use format;
  use print;
  use format-out;
  export btree-lookup, $empty-btree,
    btree-update, <btree>;
end module binary-tree;

define module miniKanren
  use common-dylan;
  use format;
  use format-out;
  use print;
  use llrb-tree;
  export
    eqeq, conj, disj,
    conde, fresh, run, run*
end module miniKanren;
