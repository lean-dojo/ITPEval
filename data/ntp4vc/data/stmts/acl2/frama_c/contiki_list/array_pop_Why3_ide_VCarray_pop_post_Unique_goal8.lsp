;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/array_pop_Why3_ide_VCarray_pop_post_Unique_goal8:
;; distinctness of two differently indexed havoced pointer-array entries after
;; array pop, under the linked-list, memory-validity, and separation invariants.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun apg8-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun apg8-address-base (address)
  (car address))

(defun apg8-address-offset (address)
  (cdr address))

(defun apg8-shift (address amount)
  (cons
   (apg8-address-base address)
   (+ (apg8-address-offset address) amount)))

;; These conservative function symbols represent the universally arbitrary
;; source functions t_2, t_3, and t, together with the fixed arbitrary region
;; and linked symbols from the memory theory.

(defstub apg8-t2 (address) t)
(defstub apg8-t3 (address) t)
(defstub apg8-malloc (index) t)
(defstub apg8-region (base) t)
(defstub apg8-linked-op () t)

(defun-sk apg8-pointer-functions-p ()
  (forall (address)
    (implies
     (apg8-address-p address)
     (and
      (apg8-address-p (apg8-t2 address))
      (apg8-address-p (apg8-t3 address))))))

(defun-sk apg8-malloc-function-p ()
  (forall (index)
    (implies
     (integerp index)
     (integerp (apg8-malloc index)))))

(defun-sk apg8-region-function-p ()
  (forall (base)
    (implies
     (integerp base)
     (integerp (apg8-region base)))))

(defun apg8-linked-p ()
  (if (apg8-linked-op) t nil))

(defun apg8-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun apg8-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (apg8-address-base left)
     (apg8-address-base right)))
   (<=
    (+ (apg8-address-offset right) right-length)
    (apg8-address-offset left))
   (<=
    (+ (apg8-address-offset left) left-length)
    (apg8-address-offset right))))

(defun apg8-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (apg8-address-base address))
    (<= 0 (apg8-address-offset address))
    (<=
     (+ (apg8-address-offset address) length)
     (apg8-malloc (apg8-address-base address))))))

;; HAVOC is the source memory-theory operation: inside the possibly modified
;; interval it reads t_2, and at every separated address it reads t_3.

(defun apg8-havoc-read
    (havoc-start havoc-length address)
  (if
      (apg8-separated-p address 1 havoc-start havoc-length)
      (apg8-t3 address)
    (apg8-t2 address)))

(defun apg8-mptr-read
    (memory-kind havoc-start havoc-length address)
  (cond
   ((equal memory-kind :t3)
    (apg8-t3 address))
   ((equal memory-kind :a5)
    (apg8-havoc-read havoc-start havoc-length address))
   (t nil)))

;; This recursion is equivalent to the source inductive p_linked_n relation:
;; n = 0 is exactly its bound constructor, while n > 0 is exactly its cons
;; constructor followed by the unique recursive predecessor at n - 1.

(defun apg8-p-linked-n-p
    (memory-kind havoc-start havoc-length
                 root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (member-eq memory-kind '(:t3 :a5))
   (apg8-address-p root)
   (apg8-address-p array)
   (integerp index)
   (integerp n)
   (apg8-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (apg8-mptr-read
        memory-kind havoc-start havoc-length
        (apg8-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (apg8-valid-rw-p root 4)
      (apg8-p-linked-n-p
       memory-kind havoc-start havoc-length
       (apg8-mptr-read
        memory-kind havoc-start havoc-length
        (apg8-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

(defun-sk apg8-framed-p ()
  (forall (address)
    (implies
     (apg8-address-p address)
     (<=
      (apg8-region
       (apg8-address-base (apg8-t3 address)))
      0))))

(defun-sk apg8-array-swipe-left-p
    (havoc-start havoc-length array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (equal
      (apg8-t3 (apg8-shift array (+ 1 index)))
      (apg8-havoc-read
       havoc-start havoc-length
       (apg8-shift array index))))))

;; In both source p_unchanged hypotheses, the malloc function and real-valued
;; memory t_1 are identical on the two sides. After unfolding load_s1_list and
;; eqs1_list, equality of the selected addresses makes the real-field
;; equalities automatic; the next-pointer equality and valid_rw implication
;; remain explicit.

(defun-sk apg8-unchanged-p
    (havoc-start havoc-length array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (let*
         ((slot (apg8-shift array index))
          (left-address
           (apg8-havoc-read
            havoc-start havoc-length slot))
          (right-address (apg8-t3 slot)))
       (and
        (equal left-address right-address)
        (equal
         (apg8-t3 (apg8-shift right-address 0))
         (apg8-havoc-read
          havoc-start havoc-length
          (apg8-shift left-address 0)))
        (implies
         (apg8-valid-rw-p right-address 4)
         (apg8-valid-rw-p left-address 4)))))))

(defun-sk apg8-a1-separated-range-p
    (a1 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (apg8-separated-p
      a1 1
      (apg8-t3 (apg8-shift array index))
      4))))

(defun-sk apg8-array-separated-range-p
    (array-base array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (apg8-separated-p
      (apg8-t3 (apg8-shift array index))
      4 array-base 2147483646))))

(defun-sk apg8-range-addresses-distinct-p
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
       (apg8-t3 (apg8-shift array left-index))
       (apg8-t3 (apg8-shift array right-index)))))))

(defun-sk apg8-range-addresses-separated-p
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
     (apg8-separated-p
      (apg8-t3 (apg8-shift array left-index))
      4
      (apg8-t3 (apg8-shift array right-index))
      4))))

(defun-sk
    ntp4vc-array-pop-post-unique-goal8-statement ()
  (forall
   (a4 i2 i a1 i5 i1 i4 i3 a a3 a2)
   (implies
    (and
     (apg8-pointer-functions-p)
     (apg8-malloc-function-p)
     (apg8-region-function-p)
     (apg8-address-p a4)
     (integerp i2)
     (integerp i)
     (apg8-address-p a1)
     (integerp i5)
     (integerp i1)
     (integerp i4)
     (integerp i3)
     (apg8-address-p a)
     (apg8-address-p a3)
     (apg8-address-p a2))
    (let*
        ((havoc-start (apg8-shift a4 i2))
         (havoc-length (- i 1))
         (a6 (apg8-t3 a1))
         (x (+ i i2))
         (x1 (+ 1 i5))
         (a7 (apg8-shift a4 0))
         (a8 (apg8-t3 (apg8-shift a4 i1)))
         (x2 (- i2 i1)))
      (implies
       (and
        (not (equal i4 i3))
        (equal
         (apg8-havoc-read havoc-start havoc-length a1)
         a6)
        (< 0 i)
        (<= 0 i1)
        (<= i1 i2)
        (<= i1 i3)
        (<= i1 i4)
        (<= i2 i5)
        (< i5 x)
        (<= (apg8-region (apg8-address-base a)) 0)
        (<= (apg8-region (apg8-address-base a1)) 0)
        (<= (apg8-region (apg8-address-base a3)) 0)
        (<= (apg8-region (apg8-address-base a4)) 0)
        (<= (+ 2 i3) x)
        (<= (+ 2 i4) x)
        (<= x x1)
        (apg8-framed-p)
        (apg8-linked-p)
        (apg8-is-sint32-p i)
        (apg8-is-sint32-p i1)
        (apg8-is-sint32-p i2)
        (apg8-is-sint32-p i5)
        (apg8-valid-rw-p a7 2147483646)
        (apg8-separated-p a1 1 a7 2147483646)
        (apg8-separated-p a6 4 a7 2147483646)
        (apg8-p-linked-n-p
         :t3 havoc-start havoc-length
         a a4 i2 i a3)
        (apg8-p-linked-n-p
         :t3 havoc-start havoc-length
         a8 a4 i1 x2 a)
        (apg8-array-swipe-left-p
         havoc-start havoc-length a4 i2 i5)
        (apg8-p-linked-n-p
         :a5 havoc-start havoc-length
         a2 a4 x1 (- (- (+ i i2) 1) i5) a3)
        (apg8-p-linked-n-p
         :a5 havoc-start havoc-length
         a8 a4 i1 x2 a)
        (apg8-p-linked-n-p
         :a5 havoc-start havoc-length
         (apg8-havoc-read
          havoc-start havoc-length
          (apg8-shift a 0))
         a4 i2 (- i5 i2) a2)
        (apg8-unchanged-p
         havoc-start havoc-length a4 i1 i2)
        (apg8-unchanged-p
         havoc-start havoc-length a4 i5 x)
        (apg8-a1-separated-range-p a1 a4 i1 x)
        (apg8-array-separated-range-p a7 a4 i1 x)
        (apg8-range-addresses-distinct-p a4 i1 x)
        (apg8-range-addresses-separated-p a4 i1 x))
       (not
        (equal
         (apg8-havoc-read
          havoc-start havoc-length
          (apg8-shift a4 i4))
         (apg8-havoc-read
          havoc-start havoc-length
          (apg8-shift a4 i3)))))))))

(value-triple :itpeval-statement-checked)
:q
