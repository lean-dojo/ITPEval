;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/array_pop_Why3_ide_VCarray_pop_loop_inv_LeftLinked_preserved_goal17:
;; preservation of the left linked-list loop invariant after a havoced
;; pointer-array cell is updated during array pop. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun apg17-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun apg17-address-base (address)
  (car address))

(defun apg17-address-offset (address)
  (cdr address))

(defun apg17-shift (address amount)
  (cons
   (apg17-address-base address)
   (+ (apg17-address-offset address) amount)))

;; These conservative function symbols represent the universally arbitrary
;; source functions t_2, t_3, and t, together with the fixed arbitrary region
;; and linked symbols from the memory theory.

(defstub apg17-t2 (address) t)
(defstub apg17-t3 (address) t)
(defstub apg17-malloc (index) t)
(defstub apg17-region (base) t)
(defstub apg17-linked-op () t)

(defun-sk apg17-pointer-functions-p ()
  (forall (address)
    (implies
     (apg17-address-p address)
     (and
      (apg17-address-p (apg17-t2 address))
      (apg17-address-p (apg17-t3 address))))))

(defun-sk apg17-malloc-function-p ()
  (forall (index)
    (implies
     (integerp index)
     (integerp (apg17-malloc index)))))

(defun-sk apg17-region-function-p ()
  (forall (base)
    (implies
     (integerp base)
     (integerp (apg17-region base)))))

(defun apg17-linked-p ()
  (if (apg17-linked-op) t nil))

(defun apg17-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun apg17-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (apg17-address-base left)
     (apg17-address-base right)))
   (<=
    (+ (apg17-address-offset right) right-length)
    (apg17-address-offset left))
   (<=
    (+ (apg17-address-offset left) left-length)
    (apg17-address-offset right))))

(defun apg17-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (apg17-address-base address))
    (<= 0 (apg17-address-offset address))
    (<=
     (+ (apg17-address-offset address) length)
     (apg17-malloc (apg17-address-base address))))))

;; HAVOC is the source memory-theory operation: inside the possibly modified
;; interval it reads t_2, and at every separated address it reads t_3.

(defun apg17-havoc-read
    (havoc-start havoc-length address)
  (if
      (apg17-separated-p address 1 havoc-start havoc-length)
      (apg17-t3 address)
    (apg17-t2 address)))

;; A10 is the exact single functional update of A5. These three cases are
;; only names for the source functions t_3, a_5, and a_10; the arbitrary base
;; functions themselves remain the conservative function symbols above.

(defun apg17-a10-read
    (havoc-start havoc-length update-address update-value address)
  (if (equal address update-address)
      update-value
    (apg17-havoc-read havoc-start havoc-length address)))

(defun apg17-mptr-read
    (memory-kind havoc-start havoc-length
                 update-address update-value address)
  (cond
   ((equal memory-kind :t3)
    (apg17-t3 address))
   ((equal memory-kind :a5)
    (apg17-havoc-read havoc-start havoc-length address))
   ((equal memory-kind :a10)
    (apg17-a10-read
     havoc-start havoc-length
     update-address update-value address))
   (t nil)))

;; This recursion is equivalent to the source inductive p_linked_n relation:
;; n = 0 is exactly its bound constructor, while n > 0 is exactly its cons
;; constructor followed by the unique recursive predecessor at n - 1.

(defun apg17-p-linked-n-p
    (memory-kind havoc-start havoc-length
                 update-address update-value
                 root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (member-eq memory-kind '(:t3 :a5 :a10))
   (apg17-address-p root)
   (apg17-address-p array)
   (integerp index)
   (integerp n)
   (apg17-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (apg17-mptr-read
        memory-kind havoc-start havoc-length
        update-address update-value
        (apg17-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (apg17-valid-rw-p root 4)
      (apg17-p-linked-n-p
       memory-kind havoc-start havoc-length
       update-address update-value
       (apg17-mptr-read
        memory-kind havoc-start havoc-length
        update-address update-value
        (apg17-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

(defun-sk apg17-framed-p ()
  (forall (address)
    (implies
     (apg17-address-p address)
     (<=
      (apg17-region
       (apg17-address-base (apg17-t3 address)))
      0))))

(defun-sk apg17-array-swipe-left-p
    (havoc-start havoc-length array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (equal
      (apg17-t3 (apg17-shift array (+ 1 index)))
      (apg17-havoc-read
       havoc-start havoc-length
       (apg17-shift array index))))))

;; In both source p_unchanged hypotheses, the malloc function and real-valued
;; memory are identical on the two sides. After unfolding load_s1_list and
;; eqs1_list, the real equalities follow from the first address equality. The
;; remaining next-pointer equality and valid_rw implication are explicit here.

(defun-sk apg17-unchanged-p
    (havoc-start havoc-length array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (let*
         ((slot (apg17-shift array index))
          (left-address
           (apg17-havoc-read
            havoc-start havoc-length slot))
          (right-address (apg17-t3 slot)))
       (and
        (equal left-address right-address)
        (equal
         (apg17-t3 (apg17-shift right-address 0))
         (apg17-havoc-read
          havoc-start havoc-length
          (apg17-shift left-address 0)))
        (implies
         (apg17-valid-rw-p right-address 4)
         (apg17-valid-rw-p left-address 4)))))))

(defun-sk apg17-a1-separated-range-p
    (a1 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (apg17-separated-p
      a1 1
      (apg17-t3 (apg17-shift array index))
      4))))

(defun-sk apg17-array-separated-range-p
    (array-base array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (apg17-separated-p
      (apg17-t3 (apg17-shift array index))
      4 array-base 2147483646))))

(defun-sk apg17-range-addresses-distinct-p
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
       (apg17-t3 (apg17-shift array left-index))
       (apg17-t3 (apg17-shift array right-index)))))))

(defun-sk apg17-range-addresses-separated-p
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
     (apg17-separated-p
      (apg17-t3 (apg17-shift array left-index))
      4
      (apg17-t3 (apg17-shift array right-index))
      4))))

(defun-sk
    ntp4vc-array-pop-loop-inv-leftlinked-preserved-goal17-statement ()
  (forall
   (a4 i2 i a1 i1 i3 a a3 a2)
   (implies
    (and
     (apg17-pointer-functions-p)
     (apg17-malloc-function-p)
     (apg17-region-function-p)
     (apg17-address-p a4)
     (integerp i2)
     (integerp i)
     (apg17-address-p a1)
     (integerp i1)
     (integerp i3)
     (apg17-address-p a)
     (apg17-address-p a3)
     (apg17-address-p a2))
    (let*
        ((havoc-start (apg17-shift a4 i2))
         (havoc-length (- i 1))
         (a6 (apg17-t3 a1))
         (x (+ i i2))
         (a7 (apg17-shift a4 0))
         (a8 (apg17-t3 (apg17-shift a4 i1)))
         (x1 (- i2 i1))
         (x2 (+ 1 i3))
         (update-address (apg17-shift a4 i3))
         (update-value
          (apg17-havoc-read
           havoc-start havoc-length
           (apg17-shift a4 x2))))
      (implies
       (and
        (equal
         (apg17-havoc-read havoc-start havoc-length a1)
         a6)
        (< 0 i)
        (<= 0 i1)
        (<= i1 i2)
        (<= i2 i3)
        (< i3 x)
        (<= (apg17-region (apg17-address-base a)) 0)
        (<= (apg17-region (apg17-address-base a1)) 0)
        (<= (apg17-region (apg17-address-base a3)) 0)
        (<= (apg17-region (apg17-address-base a4)) 0)
        (<= (+ 2 i3) x)
        (apg17-framed-p)
        (apg17-linked-p)
        (apg17-is-sint32-p i)
        (apg17-is-sint32-p i1)
        (apg17-is-sint32-p i2)
        (apg17-is-sint32-p i3)
        (apg17-valid-rw-p a7 2147483646)
        (apg17-separated-p a1 1 a7 2147483646)
        (apg17-separated-p a6 4 a7 2147483646)
        (apg17-p-linked-n-p
         :t3 havoc-start havoc-length nil nil
         a a4 i2 i a3)
        (apg17-p-linked-n-p
         :t3 havoc-start havoc-length nil nil
         a8 a4 i1 x1 a)
        (apg17-array-swipe-left-p
         havoc-start havoc-length a4 i2 i3)
        (apg17-p-linked-n-p
         :a5 havoc-start havoc-length nil nil
         a2 a4 x2 (- (- (+ i i2) 1) i3) a3)
        (apg17-p-linked-n-p
         :a5 havoc-start havoc-length nil nil
         a8 a4 i1 x1 a)
        (apg17-p-linked-n-p
         :a5 havoc-start havoc-length nil nil
         (apg17-havoc-read
          havoc-start havoc-length
          (apg17-shift a 0))
         a4 i2 (- i3 i2) a2)
        (apg17-unchanged-p
         havoc-start havoc-length a4 i1 i2)
        (apg17-unchanged-p
         havoc-start havoc-length a4 i3 x)
        (apg17-a1-separated-range-p a1 a4 i1 x)
        (apg17-array-separated-range-p a7 a4 i1 x)
        (apg17-range-addresses-distinct-p a4 i1 x)
        (apg17-range-addresses-separated-p a4 i1 x))
       (apg17-p-linked-n-p
        :a10 havoc-start havoc-length
        update-address update-value
        a8 a4 i1 x1 a))))))

(value-triple :itpeval-statement-checked)

:q
