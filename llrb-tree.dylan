Module: llrb-tree
Author: David Kahn
Copyright: Copyright (c) 2015 David Kahn. See LICENSE for details.

define class <btree> (<object>)
end class;

define constant $red = #t;
define constant $black = #f;

define class <btree-branch> (<btree>)
  constant slot color :: <boolean>, required-init-keyword: color:;
  constant slot key :: <integer>, required-init-keyword: key:;
  constant slot val, required-init-keyword: val:;
  constant slot left :: <btree>, required-init-keyword: left:;
  constant slot right :: <btree>, required-init-keyword: right:;
end class;

define class <btree-empty> (<btree>)
end class;

define constant $empty-btree = make(<btree-empty>);

define class <btree-not-found> (<object>)
end class;

define constant $btree-not-found = make(<btree-not-found>);


define function btree-lookup (k :: <integer>, btree :: <btree>) => (value)
  if (instance?(btree, <btree-empty>))
    $btree-not-found;
  else
    let btree :: <btree-branch> = btree;
    case
      (k == btree.key) => btree.val;
      (k > btree.key) => btree-lookup(k, btree.right);
      otherwise => btree-lookup(k, btree.left);
    end case;
  end if;
end function;

define function red? (btree :: <btree>)
  if (instance?(btree, <btree-empty>))
    #f
  else
    let btree :: <btree-branch> = btree;
    btree.color;
  end
end;

define function color-flip (btree :: <btree-branch>)
  let l = btree.left;
  let r = btree.right;
  let left^ = make(<btree-branch>, color: ~l.color,
                   key: l.key, val: l.val, right: l.right, left: l.left);
  let right^ = make(<btree-branch>, color: ~r.color,
                    key: r.key, val: r.val, right: r.right, left: r.left);
  make(<btree-branch>,
       color: ~btree.color,
       left: left^,
       right: right^,
       key: btree.key, val: btree.val);
end;

define function rotate-left (btree :: <btree>)
  let r = btree.right;
  let h = make(<btree-branch>,
               color: $red, key: btree.key, val:  btree.val, left: btree.left, right: r.left);
  make(<btree-branch>,
       color: btree.color,
       key: r.key, val: r.val, left: h, right: r.right);
end;

define function rotate-right (btree :: <btree>)
  let l = btree.left;
  let h = make(<btree-branch>,
               color: $red, key: btree.key, val: btree.val, left: l.right, right: btree.right);
  make(<btree-branch>,
       color: btree.color,
       key: l.key, val: l.val, left: l.left, right: h);
end;

define function btree-update (k :: <integer>, v, btree :: <btree>)
  let h = btree-update%(k, v, btree);
  make(<btree-branch>, color: $black, key: h.key, val: h.val, left: h.left, right: h.right);
end;

define function btree-update% (k :: <integer>, v, btree :: <btree>)
 => (updated-tree :: <btree>)
  if (instance?(btree, <btree-empty>))
    make(<btree-branch>, key: k, val: v, left: $empty-btree, right: $empty-btree, color: $red);
  else
    let btree :: <btree-branch> = btree;

    if (red?(btree.left) & red?(btree.right))
      btree := color-flip(btree);
    end;

    case
      (k == btree.key) =>
        begin
        btree := make(<btree-branch>, key: k, val: v, left: btree.left, right: btree.right, color: btree.color);
          end;
      (k > btree.key) =>
        begin
          let right^ :: <btree-branch> = btree-update%(k, v, btree.right);
          btree := make(<btree-branch>, key: btree.key, val: btree.val, left: btree.left, right: right^, color: btree.color);
        end;
      otherwise =>
        begin
          let left^ :: <btree-branch> = btree-update%(k, v, btree.left);
          btree := make(<btree-branch>, key: btree.key, val: btree.val, left: left^, right: btree.right, color: btree.color);
        end;
    end case;

    if (red?(btree.right) & ~red?(btree.left))
      btree := rotate-left(btree);
    end;
    if (red?(btree.left) & red?(btree.left.left))
      btree := rotate-right(btree);
    end;

    btree;
  end if;
end function;

define function btree-size (btree :: <btree>) => (size :: <integer>)
  case
    instance?(btree, <btree-branch>) =>
      (btree-size(btree.left) + 1 + btree-size(btree.right));
    otherwise => 0;
  end case;
end;

define method size (object :: <btree>) => (size :: <integer>)
  btree-size(object);
end;

define method print-object (btree :: <btree-empty>, stream :: <stream>) => ()
end;

define method print-object (btree :: <btree-branch>, stream :: <stream>) => ()
  print-object(btree.left, stream);
  format(stream, "(%s %s)", btree.key, btree.val);
  print-object(btree.right, stream);
end;
