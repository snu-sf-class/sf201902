## Explain How Red-Black Tree Works (Redblack.v)

First, let's define a notion of *weakly red-black tree*.
A tree is *weakly red-black* if

1. There is the same number of black nodes on any path from the root to each leaf.
2. Except the root node, a red node cannot have a red child.

Note that a red-black tree t is also weakly red-black.

We'll say that a weakly red-black tree t is
- *red-red*(RR) if its root is red with a red child
- *red*(R) if the root is red without a red child
- *black*(B) if the root is black.
Note that t is just a red-black tree in this case.

```
(* excerpted from Redblack.v *)
Definition balance rb t1 k vk t2 :=
 match rb with Red ⇒ T Red t1 k vk t2
 | _ ⇒
 match t1 with
 | T Red (T Red a x vx b) y vy c ⇒
      T Red (T Black a x vx b) y vy (T Black c k vk t2)
 | T Red a x vx (T Red b y vy c) ⇒
      T Red (T Black a x vx b) y vy (T Black c k vk t2)
 | a ⇒ match t2 with
            | T Red (T Red b y vy c) z vz d ⇒
                T Red (T Black t1 k vk b) y vy (T Black c z vz d)
            | T Red b y vy (T Red c z vz d) ⇒
                T Red (T Black t1 k vk b) y vy (T Black c z vz d)
            | _ ⇒ T Black t1 k vk t2
            end
  end
 end.
 
Definition makeBlack t :=
  match t with
  | E ⇒ E
  | T _ a x vx b ⇒ T Black a x vx b
  end.
  
Fixpoint ins x vx s :=
 match s with
 | E ⇒ T Red E x vx E
 | T c a y vy b ⇒ if ltb x y then balance c (ins x vx a) y vy b
                        else if ltb y x then balance c a y vy (ins x vx b)
                        else T c a x vx b
 end.
Definition insert x vx s := makeBlack (ins x vx s).
```

We'll show that a function `ins x vx t` always return a weakly red-black tree, given that t is a red-black tree.

First of all, a function `balance rb t1 k vk t2` always returns a weakly red-black tree, given that
either t1 or t2 is a weakly red-black tree, but not both.

Assume that t1 is the weakly red-black tree.
t1 is either RR, R, or B.
- If rb is red,
    + If t1 is B, it returns R.
    + If t1 is R, it returns RR.
    + **t1 cannot be RR, We'll show this below**.
- If rb is black,
    + If t1 is RR, it returns R.
    + If t1 is B, it returns B. If t1 is R, it returns R.

The reason why t1 cannot be RR is as follows.
t1 is the result of another balance call, say `balance rb' t1' k' vk' t2'`.
To be RR, the only possible case is when its root (`rb'`) was already red.
If `rb'` is red, `rb` cannot be red, so the case is unreachable, except when `rb`
is the color of the whole tree's root.

If `rb` points to the red-black tree's root, it is always black in the execution because
`ins x vx t` starts with a red-black tree, not a weakly red-black tree.

`ins x vx t` either returns the result from `balance` or never changes colors of its nodes,
so it returns a weakly red-black tree.

`insert x vx s` colors the root with black, so it returns a red-black tree!
