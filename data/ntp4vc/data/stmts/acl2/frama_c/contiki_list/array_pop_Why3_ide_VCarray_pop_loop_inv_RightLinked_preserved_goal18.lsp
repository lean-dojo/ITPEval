;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/array_pop_Why3_ide_VCarray_pop_loop_inv_RightLinked_preserved_goal18:
;; preservation of the right linked-list loop invariant after a havoced
;; pointer-array cell is updated during array pop. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun apg18-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun apg18-address-base (address)
  (car address))

(defun apg18-address-offset (address)
  (cdr address))

(defun apg18-shift (address amount)
  (cons
   (apg18-address-base address)
   (+ (apg18-address-offset address) amount)))

;; These conservative function symbols represent the universally arbitrary
;; source functions t_2, t_3, and t, together with the fixed arbitrary region
;; and linked symbols from the memory theory.

(defstub apg18-t2 (address) t)
(defstub apg18-t3 (address) t)
(defstub apg18-malloc (index) t)
(defstub apg18-region (base) t)
(defstub apg18-linked-op () t)

(defun-sk apg18-pointer-functions-p ()
  (forall (address)
    (implies
     (apg18-address-p address)
     (and
      (apg18-address-p (apg18-t2 address))
      (apg18-address-p (apg18-t3 address))))))

(defun-sk apg18-malloc-function-p ()
  (forall (index)
    (implies
     (integerp index)
     (integerp (apg18-malloc index)))))

(defun-sk apg18-region-function-p ()
  (forall (base)
    (implies
     (integerp base)
     (integerp (apg18-region base)))))

(defun apg18-linked-p ()
  (if (apg18-linked-op) t nil))

(defun apg18-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun apg18-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (apg18-address-base left)
     (apg18-address-base right)))
   (<=
    (+ (apg18-address-offset right) right-length)
    (apg18-address-offset left))
   (<=
    (+ (apg18-address-offset left) left-length)
    (apg18-address-offset right))))

(defun apg18-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (apg18-address-base address))
    (<= 0 (apg18-address-offset address))
    (<=
     (+ (apg18-address-offset address) length)
     (apg18-malloc (apg18-address-base address))))))

;; HAVOC is the source memory-theory operation: inside the possibly modified
;; interval it reads t_2, and at every separated address it reads t_3.

(defun apg18-havoc-read
    (havoc-start havoc-length address)
  (if
      (apg18-separated-p address 1 havoc-start havoc-length)
      (apg18-t3 address)
    (apg18-t2 address)))

;; A9 is the exact single functional update of A5. These three cases are only
;; names for the source functions t_3, a_5, and a_9; the arbitrary base
;; functions themselves remain the conservative function symbols above.

(defun apg18-a9-read
    (havoc-start havoc-length update-address update-value address)
  (if (equal address update-address)
      update-value
    (apg18-havoc-read havoc-start havoc-length address)))

(defun apg18-mptr-read
    (memory-kind havoc-start havoc-length
                 update-address update-value address)
  (cond
   ((equal memory-kind :t3)
    (apg18-t3 address))
   ((equal memory-kind :a5)
    (apg18-havoc-read havoc-start havoc-length address))
   ((equal memory-kind :a9)
    (apg18-a9-read
     havoc-start havoc-length
     update-address update-value address))
   (t nil)))

;; This recursion is equivalent to the source inductive p_linked_n relation:
;; n = 0 is exactly its bound constructor, while n > 0 is exactly its cons
;; constructor followed by the unique recursive predecessor at n - 1.

(defun apg18-p-linked-n-p
    (memory-kind havoc-start havoc-length
                 update-address update-value
                 root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (member-eq memory-kind '(:t3 :a5 :a9))
   (apg18-address-p root)
   (apg18-address-p array)
   (integerp index)
   (integerp n)
   (apg18-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (apg18-mptr-read
        memory-kind havoc-start havoc-length
        update-address update-value
        (apg18-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (apg18-valid-rw-p root 4)
      (apg18-p-linked-n-p
       memory-kind havoc-start havoc-length
       update-address update-value
       (apg18-mptr-read
        memory-kind havoc-start havoc-length
        update-address update-value
        (apg18-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

(defun-sk apg18-framed-p ()
  (forall (address)
    (implies
     (apg18-address-p address)
     (<=
      (apg18-region
       (apg18-address-base (apg18-t3 address)))
      0))))

(defun-sk apg18-array-swipe-left-p
    (havoc-start havoc-length array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (equal
      (apg18-t3 (apg18-shift array (+ 1 index)))
      (apg18-havoc-read
       havoc-start havoc-length
       (apg18-shift array index))))))

;; In both source p_unchanged hypotheses, the malloc function and real-valued
;; memory are identical on the two sides. After unfolding load_s1_list and
;; eqs1_list, the real equalities follow from the first address equality. The
;; remaining next-pointer equality and valid_rw implication are explicit here.

(defun-sk apg18-unchanged-p
    (havoc-start havoc-length array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (let*
         ((slot (apg18-shift array index))
          (left-address
           (apg18-havoc-read
            havoc-start havoc-length slot))
          (right-address (apg18-t3 slot)))
       (and
        (equal left-address right-address)
        (equal
         (apg18-t3 (apg18-shift right-address 0))
         (apg18-havoc-read
          havoc-start havoc-length
          (apg18-shift left-address 0)))
        (implies
         (apg18-valid-rw-p right-address 4)
         (apg18-valid-rw-p left-address 4)))))))

(defun-sk apg18-a1-separated-range-p
    (a1 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (apg18-separated-p
      a1 1
      (apg18-t3 (apg18-shift array index))
      4))))

(defun-sk apg18-array-separated-range-p
    (array-base array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (apg18-separated-p
      (apg18-t3 (apg18-shift array index))
      4 array-base 2147483646))))

(defun-sk apg18-range-addresses-distinct-p
    (array lower upper)
  (forall (left-index right-index)
    (implies
     (and
      (integerp left-index)
      (integerp right-index)
      (not (equal left-index right-index))
      (<= lower right-index)
      (<= lower left-index)
      (< right-index upper)
      (< left-index upper))
     (not
      (equal
       (apg18-t3 (apg18-shift array left-index))
       (apg18-t3 (apg18-shift array right-index)))))))

(defun-sk apg18-range-addresses-separated-p
    (array lower upper)
  (forall (left-index right-index)
    (implies
     (and
      (integerp left-index)
      (integerp right-index)
      (not (equal left-index right-index))
      (<= lower right-index)
      (<= lower left-index)
      (< right-index upper)
      (< left-index upper))
     (apg18-separated-p
      (apg18-t3 (apg18-shift array left-index))
      4
      (apg18-t3 (apg18-shift array right-index))
      4))))

(defun-sk
    ntp4vc-array-pop-loop-inv-rightlinked-preserved-goal18-statement ()
  (forall
   (a4 i2 i a1 i3 i1 a a3 a2)
   (implies
    (and
     (apg18-pointer-functions-p)
     (apg18-malloc-function-p)
     (apg18-region-function-p)
     (apg18-address-p a4)
     (integerp i2)
     (integerp i)
     (apg18-address-p a1)
     (integerp i3)
     (integerp i1)
     (apg18-address-p a)
     (apg18-address-p a3)
     (apg18-address-p a2))
    (let*
        ((havoc-start (apg18-shift a4 i2))
         (havoc-length (- i 1))
         (a6 (apg18-t3 a1))
         (x (+ i i2))
         (x1 (+ 2 i3))
         (x2 (+ 1 i3))
         (a7 (apg18-shift a4 0))
         (a8 (apg18-t3 (apg18-shift a4 i1)))
         (x3 (- i2 i1))
         (update-address (apg18-shift a4 i3))
         (update-value
          (apg18-havoc-read
           havoc-start havoc-length
           (apg18-shift a4 x2))))
      (implies
       (and
        (equal
         (apg18-havoc-read havoc-start havoc-length a1)
         a6)
        (< 0 i)
        (<= 0 i1)
        (<= i1 i2)
        (<= i2 i3)
        (< i3 x)
        (<= (apg18-region (apg18-address-base a)) 0)
        (<= (apg18-region (apg18-address-base a1)) 0)
        (<= (apg18-region (apg18-address-base a3)) 0)
        (<= (apg18-region (apg18-address-base a4)) 0)
        (<= x1 x)
        (apg18-framed-p)
        (apg18-linked-p)
        (apg18-is-sint32-p i)
        (apg18-is-sint32-p i1)
        (apg18-is-sint32-p i2)
        (apg18-is-sint32-p i3)
        (apg18-is-sint32-p x2)
        (apg18-valid-rw-p a7 2147483646)
        (apg18-separated-p a1 1 a7 2147483646)
        (apg18-separated-p a6 4 a7 2147483646)
        (apg18-p-linked-n-p
         :t3 havoc-start havoc-length nil nil
         a a4 i2 i a3)
        (apg18-p-linked-n-p
         :t3 havoc-start havoc-length nil nil
         a8 a4 i1 x3 a)
        (apg18-array-swipe-left-p
         havoc-start havoc-length a4 i2 i3)
        (apg18-p-linked-n-p
         :a5 havoc-start havoc-length nil nil
         a2 a4 x2 (- (- (+ i i2) 1) i3) a3)
        (apg18-p-linked-n-p
         :a5 havoc-start havoc-length nil nil
         a8 a4 i1 x3 a)
        (apg18-p-linked-n-p
         :a5 havoc-start havoc-length nil nil
         (apg18-havoc-read
          havoc-start havoc-length
          (apg18-shift a 0))
         a4 i2 (- i3 i2) a2)
        (apg18-unchanged-p
         havoc-start havoc-length a4 i1 i2)
        (apg18-unchanged-p
         havoc-start havoc-length a4 i3 x)
        (apg18-a1-separated-range-p a1 a4 i1 x)
        (apg18-array-separated-range-p a7 a4 i1 x)
        (apg18-range-addresses-distinct-p a4 i1 x)
        (apg18-range-addresses-separated-p a4 i1 x))
       (apg18-p-linked-n-p
        :a9 havoc-start havoc-length
        update-address update-value
        (apg18-a9-read
         havoc-start havoc-length
         update-address update-value
         (apg18-shift a2 0))
        a4 x1 (- (- (+ i i2) 2) i3) a3))))))

(value-triple :itpeval-statement-checked)

:q
