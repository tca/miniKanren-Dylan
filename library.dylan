Module: dylan-user
Author: David Kahn
Copyright: Copyright (c) 2015 David Kahn. See LICENSE for details.

define library miniKanren
  use common-dylan;
  use io;

  export miniKanren;
end library miniKanren;

define module llrb-tree
  use common-dylan;
  use format;
  use print;
  use format-out;

  export btree-lookup, $btree-not-found, $empty-btree,
    btree-update, <btree>;
end module binary-tree;

define module miniKanren
  use common-dylan;
  use format;
  use format-out;
  use print;
  use llrb-tree;

  export
    eqeq, not-eqeq, absento,
    conj, disj,
    conde, fresh, run, run*
end module miniKanren;
