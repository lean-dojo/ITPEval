;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/array_pop_Why3_ide_VCarray_pop_post_Separation_2_goal7:
;; separation of two distinct havoced pointer-array entries after array pop,
;; under the linked-list, memory-validity, and range-separation invariants.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun apg7-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun apg7-address-base (address)
  (car address))

(defun apg7-address-offset (address)
  (cdr address))

(defun apg7-shift (address amount)
  (cons
   (apg7-address-base address)
   (+ (apg7-address-offset address) amount)))

;; These conservative function symbols represent the universally arbitrary
;; source functions t_2, t_3, and t, together with the fixed arbitrary region
;; and linked symbols from the memory theory.

(defstub apg7-t2 (address) t)
(defstub apg7-t3 (address) t)
(defstub apg7-malloc (index) t)
(defstub apg7-region (base) t)
(defstub apg7-linked-op () t)

(defun-sk apg7-pointer-functions-p ()
  (forall (address)
    (implies
     (apg7-address-p address)
     (and
      (apg7-address-p (apg7-t2 address))
      (apg7-address-p (apg7-t3 address))))))

(defun-sk apg7-malloc-function-p ()
  (forall (index)
    (implies
     (integerp index)
     (integerp (apg7-malloc index)))))

(defun-sk apg7-region-function-p ()
  (forall (base)
    (implies
     (integerp base)
     (integerp (apg7-region base)))))

(defun apg7-linked-p ()
  (if (apg7-linked-op) t nil))

(defun apg7-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun apg7-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (apg7-address-base left)
     (apg7-address-base right)))
   (<=
    (+ (apg7-address-offset right) right-length)
    (apg7-address-offset left))
   (<=
    (+ (apg7-address-offset left) left-length)
    (apg7-address-offset right))))

(defun apg7-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (apg7-address-base address))
    (<= 0 (apg7-address-offset address))
    (<=
     (+ (apg7-address-offset address) length)
     (apg7-malloc (apg7-address-base address))))))

;; HAVOC is the source memory-theory operation: inside the possibly modified
;; interval it reads t_2, and at every separated address it reads t_3.

(defun apg7-havoc-read
    (havoc-start havoc-length address)
  (if
      (apg7-separated-p address 1 havoc-start havoc-length)
      (apg7-t3 address)
    (apg7-t2 address)))

(defun apg7-mptr-read
    (memory-kind havoc-start havoc-length address)
  (cond
   ((equal memory-kind :t3)
    (apg7-t3 address))
   ((equal memory-kind :a5)
    (apg7-havoc-read havoc-start havoc-length address))
   (t nil)))

;; This recursion is equivalent to the source inductive p_linked_n relation:
;; n = 0 is exactly its bound constructor, while n > 0 is exactly its cons
;; constructor followed by the unique recursive predecessor at n - 1.

(defun apg7-p-linked-n-p
    (memory-kind havoc-start havoc-length
                 root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (member-eq memory-kind '(:t3 :a5))
   (apg7-address-p root)
   (apg7-address-p array)
   (integerp index)
   (integerp n)
   (apg7-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (apg7-mptr-read
        memory-kind havoc-start havoc-length
        (apg7-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (apg7-valid-rw-p root 4)
      (apg7-p-linked-n-p
       memory-kind havoc-start havoc-length
       (apg7-mptr-read
        memory-kind havoc-start havoc-length
        (apg7-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

(defun-sk apg7-framed-p ()
  (forall (address)
    (implies
     (apg7-address-p address)
     (<=
      (apg7-region
       (apg7-address-base (apg7-t3 address)))
      0))))

(defun-sk apg7-array-swipe-left-p
    (havoc-start havoc-length array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (equal
      (apg7-t3 (apg7-shift array (+ 1 index)))
      (apg7-havoc-read
       havoc-start havoc-length
       (apg7-shift array index))))))

;; In both source p_unchanged hypotheses, the malloc function and real-valued
;; memory t_1 are identical on the two sides. After unfolding load_s1_list and
;; eqs1_list, equality of the selected addresses makes the real-field
;; equalities automatic; the next-pointer equality and valid_rw implication
;; remain explicit.

(defun-sk apg7-unchanged-p
    (havoc-start havoc-length array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (let*
         ((slot (apg7-shift array index))
          (left-address
           (apg7-havoc-read
            havoc-start havoc-length slot))
          (right-address (apg7-t3 slot)))
       (and
        (equal left-address right-address)
        (equal
         (apg7-t3 (apg7-shift right-address 0))
         (apg7-havoc-read
          havoc-start havoc-length
          (apg7-shift left-address 0)))
        (implies
         (apg7-valid-rw-p right-address 4)
         (apg7-valid-rw-p left-address 4)))))))

(defun-sk apg7-a1-separated-range-p
    (a1 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (apg7-separated-p
      a1 1
      (apg7-t3 (apg7-shift array index))
      4))))

(defun-sk apg7-array-separated-range-p
    (array-base array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (apg7-separated-p
      (apg7-t3 (apg7-shift array index))
      4 array-base 2147483646))))

(defun-sk apg7-range-addresses-distinct-p
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
       (apg7-t3 (apg7-shift array left-index))
       (apg7-t3 (apg7-shift array right-index)))))))

(defun-sk apg7-range-addresses-separated-p
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
     (apg7-separated-p
      (apg7-t3 (apg7-shift array left-index))
      4
      (apg7-t3 (apg7-shift array right-index))
      4))))

(defun-sk
    ntp4vc-array-pop-post-separation-2-goal7-statement ()
  (forall
   (a4 i2 i a1 i5 i1 i4 i3 a a3 a2)
   (implies
    (and
     (apg7-pointer-functions-p)
     (apg7-malloc-function-p)
     (apg7-region-function-p)
     (apg7-address-p a4)
     (integerp i2)
     (integerp i)
     (apg7-address-p a1)
     (integerp i5)
     (integerp i1)
     (integerp i4)
     (integerp i3)
     (apg7-address-p a)
     (apg7-address-p a3)
     (apg7-address-p a2))
    (let*
        ((havoc-start (apg7-shift a4 i2))
         (havoc-length (- i 1))
         (a6 (apg7-t3 a1))
         (x (+ i i2))
         (x1 (+ 1 i5))
         (a7 (apg7-shift a4 0))
         (a8 (apg7-t3 (apg7-shift a4 i1)))
         (x2 (- i2 i1)))
      (implies
       (and
        (not (equal i4 i3))
        (equal
         (apg7-havoc-read havoc-start havoc-length a1)
         a6)
        (< 0 i)
        (<= 0 i1)
        (<= i1 i2)
        (<= i1 i3)
        (<= i1 i4)
        (<= i2 i5)
        (< i5 x)
        (<= (apg7-region (apg7-address-base a)) 0)
        (<= (apg7-region (apg7-address-base a1)) 0)
        (<= (apg7-region (apg7-address-base a3)) 0)
        (<= (apg7-region (apg7-address-base a4)) 0)
        (<= (+ 2 i3) x)
        (<= (+ 2 i4) x)
        (<= x x1)
        (apg7-framed-p)
        (apg7-linked-p)
        (apg7-is-sint32-p i)
        (apg7-is-sint32-p i1)
        (apg7-is-sint32-p i2)
        (apg7-is-sint32-p i5)
        (apg7-valid-rw-p a7 2147483646)
        (apg7-separated-p a1 1 a7 2147483646)
        (apg7-separated-p a6 4 a7 2147483646)
        (apg7-p-linked-n-p
         :t3 havoc-start havoc-length
         a a4 i2 i a3)
        (apg7-p-linked-n-p
         :t3 havoc-start havoc-length
         a8 a4 i1 x2 a)
        (apg7-array-swipe-left-p
         havoc-start havoc-length a4 i2 i5)
        (apg7-p-linked-n-p
         :a5 havoc-start havoc-length
         a2 a4 x1 (- (- (+ i i2) 1) i5) a3)
        (apg7-p-linked-n-p
         :a5 havoc-start havoc-length
         a8 a4 i1 x2 a)
        (apg7-p-linked-n-p
         :a5 havoc-start havoc-length
         (apg7-havoc-read
          havoc-start havoc-length
          (apg7-shift a 0))
         a4 i2 (- i5 i2) a2)
        (apg7-unchanged-p
         havoc-start havoc-length a4 i1 i2)
        (apg7-unchanged-p
         havoc-start havoc-length a4 i5 x)
        (apg7-a1-separated-range-p a1 a4 i1 x)
        (apg7-array-separated-range-p a7 a4 i1 x)
        (apg7-range-addresses-distinct-p a4 i1 x)
        (apg7-range-addresses-separated-p a4 i1 x))
       (apg7-separated-p
        (apg7-havoc-read
         havoc-start havoc-length
         (apg7-shift a4 i4))
        4
        (apg7-havoc-read
         havoc-start havoc-length
         (apg7-shift a4 i3))
        4))))))

(value-triple :itpeval-statement-checked)

:q
