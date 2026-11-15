;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/array_pop_Why3_ide_VCarray_pop_loop_inv_CenterLinked_preserved_goal14:
;; preservation of the centered linked-list loop invariant after a havoced
;; pointer-array cell is updated during array pop. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun apg14-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun apg14-address-base (address)
  (car address))

(defun apg14-address-offset (address)
  (cdr address))

(defun apg14-shift (address amount)
  (cons
   (apg14-address-base address)
   (+ (apg14-address-offset address) amount)))

;; These conservative function symbols represent the universally arbitrary
;; source functions t_2, t_3, and t, together with the fixed arbitrary region
;; and linked symbols from the memory theory.

(defstub apg14-t2 (address) t)
(defstub apg14-t3 (address) t)
(defstub apg14-malloc (index) t)
(defstub apg14-region (base) t)
(defstub apg14-linked-op () t)

(defun-sk apg14-pointer-functions-p ()
  (forall (address)
    (implies
     (apg14-address-p address)
     (and
      (apg14-address-p (apg14-t2 address))
      (apg14-address-p (apg14-t3 address))))))

(defun-sk apg14-malloc-function-p ()
  (forall (index)
    (implies
     (integerp index)
     (integerp (apg14-malloc index)))))

(defun-sk apg14-region-function-p ()
  (forall (base)
    (implies
     (integerp base)
     (integerp (apg14-region base)))))

(defun apg14-linked-p ()
  (if (apg14-linked-op) t nil))

(defun apg14-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun apg14-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (apg14-address-base left)
     (apg14-address-base right)))
   (<=
    (+ (apg14-address-offset right) right-length)
    (apg14-address-offset left))
   (<=
    (+ (apg14-address-offset left) left-length)
    (apg14-address-offset right))))

(defun apg14-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (apg14-address-base address))
    (<= 0 (apg14-address-offset address))
    (<=
     (+ (apg14-address-offset address) length)
     (apg14-malloc (apg14-address-base address))))))

;; HAVOC is the source memory-theory operation: inside the possibly modified
;; interval it reads t_2, and at every separated address it reads t_3.

(defun apg14-havoc-read
    (havoc-start havoc-length address)
  (if
      (apg14-separated-p address 1 havoc-start havoc-length)
      (apg14-t3 address)
    (apg14-t2 address)))

;; A10 is the exact single functional update of A5.  These three cases are
;; only names for the source functions t_3, a_5, and a_10; the arbitrary base
;; functions themselves remain the conservative function symbols above.

(defun apg14-a10-read
    (havoc-start havoc-length update-address update-value address)
  (if (equal address update-address)
      update-value
    (apg14-havoc-read havoc-start havoc-length address)))

(defun apg14-mptr-read
    (memory-kind havoc-start havoc-length
                 update-address update-value address)
  (cond
   ((equal memory-kind :t3)
    (apg14-t3 address))
   ((equal memory-kind :a5)
    (apg14-havoc-read havoc-start havoc-length address))
   ((equal memory-kind :a10)
    (apg14-a10-read
     havoc-start havoc-length
     update-address update-value address))
   (t nil)))

;; This recursion is equivalent to the source inductive p_linked_n relation:
;; n = 0 is exactly its bound constructor, while n > 0 is exactly its cons
;; constructor followed by the unique recursive predecessor at n - 1.

(defun apg14-p-linked-n-p
    (memory-kind havoc-start havoc-length
                 update-address update-value
                 root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (member-eq memory-kind '(:t3 :a5 :a10))
   (apg14-address-p root)
   (apg14-address-p array)
   (integerp index)
   (integerp n)
   (apg14-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (apg14-mptr-read
        memory-kind havoc-start havoc-length
        update-address update-value
        (apg14-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (apg14-valid-rw-p root 4)
      (apg14-p-linked-n-p
       memory-kind havoc-start havoc-length
       update-address update-value
       (apg14-mptr-read
        memory-kind havoc-start havoc-length
        update-address update-value
        (apg14-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

(defun-sk apg14-framed-p ()
  (forall (address)
    (implies
     (apg14-address-p address)
     (<=
      (apg14-region
       (apg14-address-base (apg14-t3 address)))
      0))))

(defun-sk apg14-array-swipe-left-p
    (havoc-start havoc-length array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (equal
      (apg14-t3 (apg14-shift array (+ 1 index)))
      (apg14-havoc-read
       havoc-start havoc-length
       (apg14-shift array index))))))

;; In both source p_unchanged hypotheses, the malloc function and real-valued
;; memory are identical on the two sides.  After unfolding load_s1_list and
;; eqs1_list, the three real equalities and the valid_rw implication are
;; tautological once the first address equality holds.  The remaining next
;; pointer equality is retained explicitly below.

(defun-sk apg14-unchanged-p
    (havoc-start havoc-length array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (let*
         ((slot (apg14-shift array index))
          (left-address
           (apg14-havoc-read
            havoc-start havoc-length slot))
          (right-address (apg14-t3 slot)))
       (and
        (equal left-address right-address)
        (equal
         (apg14-t3 (apg14-shift right-address 0))
         (apg14-havoc-read
          havoc-start havoc-length
          (apg14-shift left-address 0)))
        (implies
         (apg14-valid-rw-p right-address 4)
         (apg14-valid-rw-p left-address 4)))))))

(defun-sk apg14-a1-separated-range-p
    (a1 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (apg14-separated-p
      a1 1
      (apg14-t3 (apg14-shift array index))
      4))))

(defun-sk apg14-array-separated-range-p
    (array-base array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (apg14-separated-p
      (apg14-t3 (apg14-shift array index))
      4 array-base 2147483646))))

(defun-sk apg14-range-addresses-distinct-p
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
       (apg14-t3 (apg14-shift array left-index))
       (apg14-t3 (apg14-shift array right-index)))))))

(defun-sk apg14-range-addresses-separated-p
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
     (apg14-separated-p
      (apg14-t3 (apg14-shift array left-index))
      4
      (apg14-t3 (apg14-shift array right-index))
      4))))

(defun-sk
    ntp4vc-array-pop-loop-inv-centerlinked-preserved-goal14-statement ()
  (forall
   (a4 i2 i a1 i3 i1 a a3 a2)
   (implies
    (and
     (apg14-pointer-functions-p)
     (apg14-malloc-function-p)
     (apg14-region-function-p)
     (apg14-address-p a4)
     (integerp i2)
     (integerp i)
     (apg14-address-p a1)
     (integerp i3)
     (integerp i1)
     (apg14-address-p a)
     (apg14-address-p a3)
     (apg14-address-p a2))
    (let*
        ((havoc-start (apg14-shift a4 i2))
         (havoc-length (- i 1))
         (a6 (apg14-t3 a1))
         (x (+ i i2))
         (x1 (+ 1 i3))
         (a7 (apg14-shift a4 0))
         (a8 (apg14-t3 (apg14-shift a4 i1)))
         (x2 (- i2 i1))
         (a9 (apg14-shift a 0))
         (update-address (apg14-shift a4 i3))
         (update-value
          (apg14-havoc-read
           havoc-start havoc-length
           (apg14-shift a4 x1))))
      (implies
       (and
        (equal
         (apg14-havoc-read havoc-start havoc-length a1)
         a6)
        (< 0 i)
        (<= 0 i1)
        (<= i1 i2)
        (<= i2 i3)
        (< i3 x)
        (<= (apg14-region (apg14-address-base a)) 0)
        (<= (apg14-region (apg14-address-base a1)) 0)
        (<= (apg14-region (apg14-address-base a3)) 0)
        (<= (apg14-region (apg14-address-base a4)) 0)
        (<= (+ 2 i3) x)
        (apg14-framed-p)
        (apg14-linked-p)
        (apg14-is-sint32-p i)
        (apg14-is-sint32-p i1)
        (apg14-is-sint32-p i2)
        (apg14-is-sint32-p i3)
        (apg14-is-sint32-p x1)
        (apg14-valid-rw-p a7 2147483646)
        (apg14-separated-p a1 1 a7 2147483646)
        (apg14-separated-p a6 4 a7 2147483646)
        (apg14-p-linked-n-p
         :t3 havoc-start havoc-length nil nil
         a a4 i2 i a3)
        (apg14-p-linked-n-p
         :t3 havoc-start havoc-length nil nil
         a8 a4 i1 x2 a)
        (apg14-array-swipe-left-p
         havoc-start havoc-length a4 i2 i3)
        (apg14-p-linked-n-p
         :a5 havoc-start havoc-length nil nil
         a2 a4 x1 (- (- (+ i i2) 1) i3) a3)
        (apg14-p-linked-n-p
         :a5 havoc-start havoc-length nil nil
         a8 a4 i1 x2 a)
        (apg14-p-linked-n-p
         :a5 havoc-start havoc-length nil nil
         (apg14-havoc-read havoc-start havoc-length a9)
         a4 i2 (- i3 i2) a2)
        (apg14-unchanged-p
         havoc-start havoc-length a4 i1 i2)
        (apg14-unchanged-p
         havoc-start havoc-length a4 i3 x)
        (apg14-a1-separated-range-p a1 a4 i1 x)
        (apg14-array-separated-range-p a7 a4 i1 x)
        (apg14-range-addresses-distinct-p a4 i1 x)
        (apg14-range-addresses-separated-p a4 i1 x))
       (apg14-p-linked-n-p
        :a10 havoc-start havoc-length
        update-address update-value
        (apg14-a10-read
         havoc-start havoc-length
         update-address update-value
         (apg14-shift a 0))
        a4
        i2
        (- (+ 1 i3) i2)
        (apg14-a10-read
         havoc-start havoc-length
         update-address update-value
         (apg14-shift a2 0))))))))

(value-triple :itpeval-statement-checked)

:q
