;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/list_add_Why3_ide_VClist_add_call_list_final_add_pre_part11_goal35:
;; four-byte write validity of the updated final list address under the
;; list-add pointer, separation, and linked-segment invariants. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lag35-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lag35-address-base (address)
  (car address))

(defun lag35-address-offset (address)
  (cdr address))

(defun lag35-shift (address amount)
  (cons
   (lag35-address-base address)
   (+ (lag35-address-offset address) amount)))

(defun lag35-null-address ()
  (cons 0 0))

;; These conservative symbols represent the universally arbitrary source
;; pointer functions t_2 and t_3, allocation function t, real-valued memory
;; t_1, region and linked operations, and l_index_of specialized to t_3.
;; Values of t_1 are used only through equality. Since the address domain is
;; countable, arbitrary ACL2 values preserve exactly the equality patterns
;; realizable by a real-valued function.

(defstub lag35-t2 (address) t)
(defstub lag35-t3 (address) t)
(defstub lag35-malloc (index) t)
(defstub lag35-t1 (address) t)
(defstub lag35-region (base) t)
(defstub lag35-linked-op () t)
(defstub lag35-l-index-of (item array down up) t)

(defun-sk lag35-pointer-functions-p ()
  (forall (address)
    (implies
     (lag35-address-p address)
     (and
      (lag35-address-p (lag35-t2 address))
      (lag35-address-p (lag35-t3 address))))))

(defun-sk lag35-malloc-function-p ()
  (forall (index)
    (implies
     (integerp index)
     (integerp (lag35-malloc index)))))

(defun-sk lag35-region-function-p ()
  (forall (base)
    (implies
     (integerp base)
     (integerp (lag35-region base)))))

(defun-sk lag35-l-index-of-type-p ()
  (forall (item array down up)
    (implies
     (and
      (lag35-address-p item)
      (lag35-address-p array)
      (integerp down)
      (integerp up))
     (integerp
      (lag35-l-index-of item array down up)))))

(defun lag35-linked-p ()
  (if (lag35-linked-op) t nil))

(defun lag35-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lag35-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (lag35-address-base left)
     (lag35-address-base right)))
   (<=
    (+ (lag35-address-offset right) right-length)
    (lag35-address-offset left))
   (<=
    (+ (lag35-address-offset left) left-length)
    (lag35-address-offset right))))

(defun lag35-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lag35-address-base address))
    (<= 0 (lag35-address-offset address))
    (<=
     (+ (lag35-address-offset address) length)
     (lag35-malloc (lag35-address-base address))))))

;; These are exactly the three source axioms characterizing l_index_of for
;; the arbitrary pointer function t_3.

(defun-sk lag35-l-index-of-laws-p ()
  (forall (item array down up)
    (implies
     (and
      (lag35-address-p item)
      (lag35-address-p array)
      (integerp down)
      (integerp up))
     (and
      (implies
       (and
        (<= up down)
        (<= 0 up))
       (equal
        (lag35-l-index-of item array down up)
        up))
      (implies
       (and
        (equal
         (lag35-t3 (lag35-shift array down))
         item)
        (<= 0 down)
        (< down up))
       (equal
        (lag35-l-index-of item array down up)
        down))
      (implies
       (and
        (not
         (equal
          (lag35-t3 (lag35-shift array down))
          item))
        (<= 0 down)
        (< down up))
       (equal
        (lag35-l-index-of item array (+ 1 down) up)
        (lag35-l-index-of item array down up)))))))

;; M is the two successive source functional updates of t_3. The second
;; update has precedence even when the update addresses alias.

(defun lag35-m-read
    (a2 a a1 a5 address)
  (let ((second-update-address
         (lag35-shift (lag35-t3 a5) 0)))
    (cond
     ((equal address second-update-address) a1)
     ((equal address a2) a)
     (t (lag35-t3 address)))))

;; A7 is the source havoc: outside the possibly modified interval it reads M,
;; and inside that interval it reads the arbitrary prior memory t_2.

(defun lag35-a7-read
    (a2 a a1 a5 havoc-start havoc-length address)
  (if
      (lag35-separated-p address 1 havoc-start havoc-length)
      (lag35-m-read a2 a a1 a5 address)
    (lag35-t2 address)))

;; A8 is the exact functional update of A7 at shift(a4,0) with null.

(defun lag35-a8-read
    (a2 a a1 a5 havoc-start havoc-length a4 address)
  (if (equal address (lag35-shift a4 0))
      (lag35-null-address)
    (lag35-a7-read
     a2 a a1 a5 havoc-start havoc-length address)))

(defun lag35-mptr-read
    (memory-kind a2 a a1 a5 havoc-start havoc-length a4 address)
  (cond
   ((equal memory-kind :t3)
    (lag35-t3 address))
   ((equal memory-kind :a7)
    (lag35-a7-read
     a2 a a1 a5 havoc-start havoc-length address))
   ((equal memory-kind :a8)
    (lag35-a8-read
     a2 a a1 a5 havoc-start havoc-length a4 address))
   (t nil)))

;; A list of N successive roots is constructor evidence for the source
;; inductive p_linked_n relation.

(defun lag35-linked-steps-p
    (memory-kind a2 a a1 a5 havoc-start havoc-length a4
                 roots root array index bound)
  (if (consp roots)
      (and
       (lag35-address-p root)
       (equal (car roots) root)
       (equal
        (lag35-mptr-read
         memory-kind a2 a a1 a5 havoc-start havoc-length a4
         (lag35-shift array index))
        root)
       (lag35-valid-rw-p root 4)
       (lag35-linked-steps-p
        memory-kind a2 a a1 a5 havoc-start havoc-length a4
        (cdr roots)
        (lag35-mptr-read
         memory-kind a2 a a1 a5 havoc-start havoc-length a4
         (lag35-shift root 0))
        array
        (+ 1 index)
        bound))
    (and
     (equal roots nil)
     (equal root bound))))

(defun-sk lag35-p-linked-n-p
    (memory-kind a2 a a1 a5 havoc-start havoc-length a4
                 root array index n bound)
  (exists (roots)
    (and
     (member-eq memory-kind '(:t3 :a7 :a8))
     (lag35-address-p root)
     (lag35-address-p array)
     (integerp index)
     (integerp n)
     (<= 0 n)
     (lag35-address-p bound)
     (<= 0 index)
     (<= (+ index n) 2147483646)
     (true-listp roots)
     (equal (len roots) n)
     (lag35-linked-steps-p
      memory-kind a2 a a1 a5 havoc-start havoc-length a4
      roots root array index bound))))

;; This unfolds load_s1_list and eqs1_list. Pointer fields are read through
;; the selected pointer memories and scalar fields through t_1.

(defun lag35-eqs1-loads-p
    (left-kind right-kind
               a2 a a1 a5 havoc-start havoc-length a4
               left-root right-root)
  (and
   (equal
    (lag35-mptr-read
     right-kind a2 a a1 a5 havoc-start havoc-length a4
     (lag35-shift right-root 0))
    (lag35-mptr-read
     left-kind a2 a a1 a5 havoc-start havoc-length a4
     (lag35-shift left-root 0)))
   (equal
    (lag35-t1 (lag35-shift right-root 1))
    (lag35-t1 (lag35-shift left-root 1)))
   (equal
    (lag35-t1 (lag35-shift right-root 2))
    (lag35-t1 (lag35-shift left-root 2)))
   (equal
    (lag35-t1 (lag35-shift right-root 3))
    (lag35-t1 (lag35-shift left-root 3)))))

(defun-sk lag35-a4-in-t3-closed-range-p
    (a4 array lower upper)
  (exists (index)
    (and
     (integerp index)
     (equal
      a4
      (lag35-t3 (lag35-shift array index)))
     (<= lower index)
     (<= index upper))))

(defun lag35-range-index-p (index lower upper closedp)
  (and
   (integerp index)
   (<= lower index)
   (if closedp
       (<= index upper)
     (< index upper))))

;; With identical real memories t_1, the scalar-field equalities in
;; p_unchanged become reflexive after the selected addresses are equal.

(defun lag35-unchanged-at-p
    (a2 a a1 a5 havoc-start havoc-length array index)
  (let*
      ((slot (lag35-shift array index))
       (left-address
        (lag35-a7-read
         a2 a a1 a5 havoc-start havoc-length slot))
       (right-address (lag35-t3 slot)))
    (and
     (equal left-address right-address)
     (equal
      (lag35-t3 (lag35-shift right-address 0))
      (lag35-a7-read
       a2 a a1 a5 havoc-start havoc-length
       (lag35-shift left-address 0)))
     (implies
      (lag35-valid-rw-p right-address 4)
      (lag35-valid-rw-p left-address 4)))))

;; This single universal predicate packages the source's universally
;; quantified framed, range, distinctness, separation, swipe, load, and
;; unchanged hypotheses. Each integer quantifier is represented by an ACL2
;; universal quantifier with an explicit integer guard.

(defun lag35-universal-hypotheses-body-p
    (a2 a a1 a5 havoc-start havoc-length a4
        array i1 x1 x2 x3 x a11
        index-left index-right address)
  (let ((in-range
         (lag35-a4-in-t3-closed-range-p
          a4 array i1 x3)))
    (and
       ;; framed t_3
       (implies
        (lag35-address-p address)
        (<=
         (lag35-region
          (lag35-address-base (lag35-t3 address)))
         0))

       ;; p_array_swipe_left, selected according to whether a4 occurs.
       (implies
        (and
         in-range
         (lag35-range-index-p index-left x1 x3 nil))
        (equal
         (lag35-t3
          (lag35-shift array (+ 1 index-left)))
         (lag35-a7-read
          a2 a a1 a5 havoc-start havoc-length
          (lag35-shift array index-left))))

       ;; A7 never contains a4 on the required half-open or closed range.
       (implies
        (and
         in-range
         (lag35-range-index-p index-left i1 x3 nil))
        (not
         (equal
          (lag35-a7-read
           a2 a a1 a5 havoc-start havoc-length
           (lag35-shift array index-left))
          a4)))
       (implies
        (and
         (not in-range)
         (lag35-range-index-p index-left i1 x3 t))
        (not
         (equal
          (lag35-a7-read
           a2 a a1 a5 havoc-start havoc-length
           (lag35-shift array index-left))
          a4)))

       ;; The two conditional p_unchanged hypotheses.
       (implies
        (and
         (not in-range)
         (lag35-range-index-p index-left i1 x nil))
        (lag35-unchanged-at-p
         a2 a a1 a5 havoc-start havoc-length
         array index-left))
       (implies
        (and
         in-range
         (lag35-range-index-p index-left i1 x2 nil))
        (lag35-unchanged-at-p
         a2 a a1 a5 havoc-start havoc-length
         array index-left))

       ;; Separation of A7 range elements from a2, a4, and the array.
       (implies
        (and
         in-range
         (lag35-range-index-p index-left i1 x3 nil))
        (and
         (lag35-separated-p
          a2 1
          (lag35-a7-read
           a2 a a1 a5 havoc-start havoc-length
           (lag35-shift array index-left))
          4)
         (lag35-separated-p
          a4 4
          (lag35-a7-read
           a2 a a1 a5 havoc-start havoc-length
           (lag35-shift array index-left))
          4)
         (lag35-separated-p
          (lag35-a7-read
           a2 a a1 a5 havoc-start havoc-length
           (lag35-shift array index-left))
          4 a11 2147483646)))
       (implies
        (and
         (not in-range)
         (lag35-range-index-p index-left i1 x3 t))
        (and
         (lag35-separated-p
          a2 1
          (lag35-a7-read
           a2 a a1 a5 havoc-start havoc-length
           (lag35-shift array index-left))
          4)
         (lag35-separated-p
          a4 4
          (lag35-a7-read
           a2 a a1 a5 havoc-start havoc-length
           (lag35-shift array index-left))
          4)
         (lag35-separated-p
          (lag35-a7-read
           a2 a a1 a5 havoc-start havoc-length
           (lag35-shift array index-left))
          4 a11 2147483646)))

       ;; Struct equality between A7 elements and T3 successor elements.
       (implies
        (and
         in-range
         (lag35-range-index-p index-left x1 x3 nil))
        (lag35-eqs1-loads-p
         :a7 :t3
         a2 a a1 a5 havoc-start havoc-length a4
         (lag35-a7-read
          a2 a a1 a5 havoc-start havoc-length
          (lag35-shift array index-left))
         (lag35-t3
          (lag35-shift array (+ 1 index-left)))))

       ;; Pairwise distinctness and separation of A7 range elements.
       (implies
        (and
         in-range
         (lag35-range-index-p index-left i1 x3 nil)
         (lag35-range-index-p index-right i1 x3 nil)
         (not (equal index-left index-right)))
        (and
         (not
          (equal
           (lag35-a7-read
            a2 a a1 a5 havoc-start havoc-length
            (lag35-shift array index-left))
           (lag35-a7-read
            a2 a a1 a5 havoc-start havoc-length
            (lag35-shift array index-right))))
         (lag35-separated-p
          (lag35-a7-read
           a2 a a1 a5 havoc-start havoc-length
           (lag35-shift array index-left))
          4
          (lag35-a7-read
           a2 a a1 a5 havoc-start havoc-length
           (lag35-shift array index-right))
          4)))
       (implies
        (and
         (not in-range)
         (lag35-range-index-p index-left i1 x3 t)
         (lag35-range-index-p index-right i1 x3 t)
         (not (equal index-left index-right)))
        (and
         (not
          (equal
           (lag35-a7-read
            a2 a a1 a5 havoc-start havoc-length
            (lag35-shift array index-left))
           (lag35-a7-read
            a2 a a1 a5 havoc-start havoc-length
            (lag35-shift array index-right))))
         (lag35-separated-p
          (lag35-a7-read
           a2 a a1 a5 havoc-start havoc-length
           (lag35-shift array index-left))
          4
          (lag35-a7-read
           a2 a a1 a5 havoc-start havoc-length
           (lag35-shift array index-right))
          4)))

       ;; Unconditional closed-range separation and distinctness for T3.
       (implies
        (lag35-range-index-p index-left i1 x3 t)
        (and
         (lag35-separated-p
          a2 1
          (lag35-t3 (lag35-shift array index-left))
          4)
         (lag35-separated-p
          (lag35-t3 (lag35-shift array index-left))
          4 a11 2147483646)
         (implies
          (not
           (equal
            a4
            (lag35-t3
             (lag35-shift array index-left))))
          (lag35-separated-p
           a4 4
           (lag35-t3
            (lag35-shift array index-left))
           4))))
       (implies
        (and
         (lag35-range-index-p index-left i1 x3 t)
         (lag35-range-index-p index-right i1 x3 t)
         (not (equal index-left index-right)))
        (and
         (not
          (equal
           (lag35-t3 (lag35-shift array index-left))
           (lag35-t3 (lag35-shift array index-right))))
         (lag35-separated-p
         (lag35-t3 (lag35-shift array index-left))
          4
          (lag35-t3 (lag35-shift array index-right))
          4))))))

(defun-sk lag35-universal-hypotheses-p
    (a2 a a1 a5 havoc-start havoc-length a4
        array i1 x1 x2 x3 x a11)
  (forall (index-left index-right address)
    (lag35-universal-hypotheses-body-p
     a2 a a1 a5 havoc-start havoc-length a4
     array i1 x1 x2 x3 x a11
     index-left index-right address)))

(defun-sk
    ntp4vc-list-add-call-list-final-add-pre-part11-goal35-statement ()
  (forall
   (a3 i2 i i1 a2 a a1)
   (implies
    (and
     (lag35-pointer-functions-p)
     (lag35-malloc-function-p)
     (lag35-region-function-p)
     (lag35-l-index-of-type-p)
     (lag35-l-index-of-laws-p)
     (lag35-address-p a3)
     (integerp i2)
     (integerp i)
     (integerp i1)
     (lag35-address-p a2)
     (lag35-address-p a)
     (lag35-address-p a1))
    (let*
        ((a4 (lag35-t3 (lag35-shift a3 i2)))
         (x (+ 1 i i1))
         (x1 (lag35-l-index-of a4 a3 i1 x))
         (x2 (- x1 1))
         (a5 (lag35-shift a3 x2))
         (a6 (lag35-t3 a5))
         (havoc-start (lag35-shift a3 x1))
         (havoc-length (- x x1))
         (a9
          (lag35-a8-read
           a2 a a1 a5 havoc-start havoc-length a4 a2))
         (a10
          (lag35-a8-read
           a2 a a1 a5 havoc-start havoc-length a4
           (lag35-shift a3 (- (+ i i1) 1))))
         (x3 (+ i i1))
         (x4 (+ 1 i))
         (a11 (lag35-shift a3 0))
         (a12 (lag35-t3 a2))
         (a13
          (lag35-a7-read
           a2 a a1 a5 havoc-start havoc-length a2))
         (in-range
          (lag35-a4-in-t3-closed-range-p
           a4 a3 i1 x3)))
      (implies
       (and
        (not (equal a4 (lag35-null-address)))
        (not (equal x x1))
        (not (equal a9 (lag35-null-address)))
        (not (equal a10 (lag35-null-address)))
        (<= 0 i1)
        (<= i1 i2)
        (<= i2 x3)
        (<= (lag35-region (lag35-address-base a2)) 0)
        (<= (lag35-region (lag35-address-base a3)) 0)
        (<= (lag35-region (lag35-address-base a4)) 0)
        (<= i1 x1)
        (<= x1 x3)
        (<= -1 i)
        (<= i 2147483644)
        (<= i1 2147483645)
        (<= x3 2147483644)
        (<= x1 x)
        (lag35-linked-p)
        (lag35-is-sint32-p i)
        (lag35-is-sint32-p i1)
        (lag35-valid-rw-p a2 1)
        (lag35-is-sint32-p x4)
        (lag35-valid-rw-p a11 2147483646)
        (lag35-valid-rw-p (lag35-shift a3 i1) x4)
        (lag35-valid-rw-p a4 4)
        (lag35-separated-p a2 1 a11 2147483646)
        (lag35-separated-p a12 4 a11 2147483646)
        (lag35-separated-p a2 1 a4 4)
        (lag35-separated-p a4 4 a11 2147483646)
        (lag35-p-linked-n-p
         :t3 a2 a a1 a5 havoc-start havoc-length a4
         a12 a3 i1 x4 (lag35-null-address))
        (lag35-is-sint32-p x1)
        (lag35-separated-p a13 4 a11 2147483646)
        (lag35-eqs1-loads-p
         :a7 :t3
         a2 a a1 a5 havoc-start havoc-length a4
         a4 a4)
        (lag35-p-linked-n-p
         :a8 a2 a a1 a5 havoc-start havoc-length a4
         a9 a3 i1 i (lag35-null-address))
        (lag35-p-linked-n-p
         :a8 a2 a a1 a5 havoc-start havoc-length a4
         a9 a3 i1 (- i 1) a10)
        (implies
         (and (< i1 x1) in-range)
         (equal
          (lag35-a7-read
           a2 a a1 a5 havoc-start havoc-length a5)
          a6))
        (implies
         in-range
         (lag35-p-linked-n-p
          :a7 a2 a a1 a5 havoc-start havoc-length a4
          a13 a3 i1 i (lag35-null-address)))
        (implies
         (not in-range)
         (lag35-p-linked-n-p
          :a7 a2 a a1 a5 havoc-start havoc-length a4
          a13 a3 i1 x4 (lag35-null-address)))
        (lag35-universal-hypotheses-p
         a2 a a1 a5 havoc-start havoc-length a4
         a3 i1 x1 x2 x3 x a11))
       (lag35-valid-rw-p a10 4))))))

(value-triple :itpeval-statement-checked)

:q
