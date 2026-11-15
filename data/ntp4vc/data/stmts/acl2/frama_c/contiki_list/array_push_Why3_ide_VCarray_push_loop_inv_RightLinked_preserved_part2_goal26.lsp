;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/array_push_Why3_ide_VCarray_push_loop_inv_RightLinked_preserved_part2_goal26:
;; preservation of the right linked-list loop invariant after a havoced
;; pointer-array cell is updated during array push. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun apg26-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun apg26-address-base (address)
  (car address))

(defun apg26-address-offset (address)
  (cdr address))

(defun apg26-shift (address amount)
  (cons
   (apg26-address-base address)
   (+ (apg26-address-offset address) amount)))

;; These conservative function symbols represent the universally arbitrary
;; source functions t_2, t_3, and t, together with the fixed arbitrary region
;; and linked symbols from the memory theory.

(defstub apg26-t2 (address) t)
(defstub apg26-t3 (address) t)
(defstub apg26-malloc (index) t)
(defstub apg26-region (base) t)
(defstub apg26-linked-op () t)

(defun-sk apg26-pointer-functions-p ()
  (forall (address)
    (implies
     (apg26-address-p address)
     (and
      (apg26-address-p (apg26-t2 address))
      (apg26-address-p (apg26-t3 address))))))

(defun-sk apg26-malloc-function-p ()
  (forall (index)
    (implies
     (integerp index)
     (integerp (apg26-malloc index)))))

(defun-sk apg26-region-function-p ()
  (forall (base)
    (implies
     (integerp base)
     (integerp (apg26-region base)))))

(defun apg26-linked-p ()
  (if (apg26-linked-op) t nil))

(defun apg26-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun apg26-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (apg26-address-base left)
     (apg26-address-base right)))
   (<=
    (+ (apg26-address-offset right) right-length)
    (apg26-address-offset left))
   (<=
    (+ (apg26-address-offset left) left-length)
    (apg26-address-offset right))))

(defun apg26-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (apg26-address-base address))
    (<= 0 (apg26-address-offset address))
    (<=
     (+ (apg26-address-offset address) length)
     (apg26-malloc (apg26-address-base address))))))

;; HAVOC is the source memory-theory operation: inside the possibly modified
;; interval it reads t_2, and at every separated address it reads t_3.

(defun apg26-havoc-read
    (havoc-start havoc-length address)
  (if
      (apg26-separated-p address 1 havoc-start havoc-length)
      (apg26-t3 address)
    (apg26-t2 address)))

;; UPDATED-READ is the exact single functional update of A5.

(defun apg26-updated-read
    (havoc-start havoc-length update-address update-value address)
  (if (equal address update-address)
      update-value
    (apg26-havoc-read havoc-start havoc-length address)))

(defun apg26-mptr-read
    (memory-kind havoc-start havoc-length
                 update-address update-value address)
  (cond
   ((equal memory-kind :t3)
    (apg26-t3 address))
   ((equal memory-kind :a5)
    (apg26-havoc-read havoc-start havoc-length address))
   ((equal memory-kind :updated)
    (apg26-updated-read
     havoc-start havoc-length
     update-address update-value address))
   (t nil)))

;; This recursion is equivalent to the source inductive p_linked_n relation:
;; n = 0 is exactly its bound constructor, while n > 0 is exactly its cons
;; constructor followed by the unique recursive predecessor at n - 1.

(defun apg26-p-linked-n-p
    (memory-kind havoc-start havoc-length
                 update-address update-value
                 root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (member-eq memory-kind '(:t3 :a5 :updated))
   (apg26-address-p root)
   (apg26-address-p array)
   (integerp index)
   (integerp n)
   (apg26-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (apg26-mptr-read
        memory-kind havoc-start havoc-length
        update-address update-value
        (apg26-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (apg26-valid-rw-p root 4)
      (apg26-p-linked-n-p
       memory-kind havoc-start havoc-length
       update-address update-value
       (apg26-mptr-read
        memory-kind havoc-start havoc-length
        update-address update-value
        (apg26-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

(defun-sk apg26-framed-p ()
  (forall (address)
    (implies
     (apg26-address-p address)
     (<=
      (apg26-region
       (apg26-address-base (apg26-t3 address)))
      0))))

(defun-sk apg26-array-swipe-right-p
    (havoc-start havoc-length array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (equal
      (apg26-t3 (apg26-shift array (- index 1)))
      (apg26-havoc-read
       havoc-start havoc-length
       (apg26-shift array index))))))

;; In p_unchanged the malloc function and real-valued memory are identical on
;; both sides. After unfolding load_s1_list and eqs1_list, the real equalities
;; follow from the first address equality. The next-pointer equality and
;; valid_rw implication are retained explicitly.

(defun-sk apg26-unchanged-p
    (havoc-start havoc-length array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (let*
         ((slot (apg26-shift array index))
          (left-address
           (apg26-havoc-read
            havoc-start havoc-length slot))
          (right-address (apg26-t3 slot)))
       (and
        (equal left-address right-address)
        (equal
         (apg26-t3 (apg26-shift right-address 0))
         (apg26-havoc-read
          havoc-start havoc-length
          (apg26-shift left-address 0)))
        (implies
         (apg26-valid-rw-p right-address 4)
         (apg26-valid-rw-p left-address 4)))))))

(defun-sk apg26-a1-separated-t3-closed-range-p
    (a1 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (<= index upper))
     (apg26-separated-p
      a1 1
      (apg26-t3 (apg26-shift array index))
      4))))

(defun-sk apg26-t3-closed-range-separated-from-array-p
    (array-base array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (<= index upper))
     (apg26-separated-p
      (apg26-t3 (apg26-shift array index))
      4 array-base 2147483646))))

(defun-sk apg26-t3-closed-range-addresses-distinct-p
    (array lower upper)
  (forall (left-index right-index)
    (implies
     (and
      (integerp left-index)
      (integerp right-index)
      (not (equal left-index right-index))
      (<= lower right-index)
      (<= lower left-index)
      (<= right-index upper)
      (<= left-index upper))
     (not
      (equal
       (apg26-t3 (apg26-shift array left-index))
       (apg26-t3 (apg26-shift array right-index)))))))

(defun-sk apg26-t3-closed-range-addresses-separated-p
    (array lower upper)
  (forall (left-index right-index)
    (implies
     (and
      (integerp left-index)
      (integerp right-index)
      (not (equal left-index right-index))
      (<= lower right-index)
      (<= lower left-index)
      (<= right-index upper)
      (<= left-index upper))
     (apg26-separated-p
      (apg26-t3 (apg26-shift array left-index))
      4
      (apg26-t3 (apg26-shift array right-index))
      4))))

(defun-sk apg26-a1-separated-a5-closed-range-p
    (a1 array lower upper havoc-start havoc-length)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (<= index upper))
     (apg26-separated-p
      a1 1
      (apg26-havoc-read
       havoc-start havoc-length
       (apg26-shift array index))
      4))))

(defun-sk apg26-a5-closed-range-separated-from-array-p
    (array-base array lower upper havoc-start havoc-length)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (<= index upper))
     (apg26-separated-p
      (apg26-havoc-read
       havoc-start havoc-length
       (apg26-shift array index))
      4 array-base 2147483646))))

(defun-sk
    ntp4vc-array-push-loop-inv-rightlinked-preserved-part2-goal26-statement ()
  (forall
   (i2 i3 a4 i1 a1 i a a3 a2)
   (implies
    (and
     (apg26-pointer-functions-p)
     (apg26-malloc-function-p)
     (apg26-region-function-p)
     (integerp i2)
     (integerp i3)
     (apg26-address-p a4)
     (integerp i1)
     (apg26-address-p a1)
     (integerp i)
     (apg26-address-p a)
     (apg26-address-p a3)
     (apg26-address-p a2))
    (let*
        ((x (+ 1 i2 i3))
         (havoc-start (apg26-shift a4 (+ 1 i1)))
         (havoc-length x)
         (a6 (apg26-t3 a1))
         (x1 (+ i1 i2 i3))
         (x2 (+ i1 i2))
         (x3 (+ 1 i1 i2))
         (a7 (apg26-shift a4 0))
         (x4 (+ 1 i1 i2 i3))
         (x5 (+ 2 i1 i2))
         (a8
          (apg26-havoc-read
           havoc-start havoc-length
           (apg26-shift a4 x2)))
         (update-address (apg26-shift a4 x3)))
      (implies
       (and
        (not (equal i2 0))
        (equal (equal i3 0) (equal i 0))
        (equal (< 0 i3) (equal i 1))
        (not (equal (+ i2 i3) -1))
        (equal
         (apg26-havoc-read havoc-start havoc-length a1)
         a6)
        (<= 0 i2)
        (<= 0 i3)
        (<= (apg26-region (apg26-address-base a)) 0)
        (<= (apg26-region (apg26-address-base a1)) 0)
        (<= (apg26-region (apg26-address-base a3)) 0)
        (<= (apg26-region (apg26-address-base a4)) 0)
        (<= -1 i2)
        (<= x1 2147483644)
        (apg26-framed-p)
        (apg26-linked-p)
        (apg26-is-sint32-p i)
        (apg26-is-sint32-p i1)
        (apg26-valid-rw-p a1 1)
        (apg26-is-sint32-p x2)
        (apg26-is-sint32-p x3)
        (apg26-is-sint32-p x)
        (apg26-valid-rw-p a7 2147483646)
        (apg26-is-sint32-p x4)
        (apg26-separated-p a1 1 a7 2147483646)
        (apg26-separated-p a6 4 a7 2147483646)
        (apg26-p-linked-n-p
         :t3 havoc-start havoc-length nil nil
         a a4 i1 x a3)
        (apg26-array-swipe-right-p
         havoc-start havoc-length
         a4 x5 (+ 2 i1 i2 i3))
        (apg26-p-linked-n-p
         :a5 havoc-start havoc-length nil nil
         a a4 i1 (+ 1 i2) a2)
        (apg26-p-linked-n-p
         :a5 havoc-start havoc-length nil nil
         a2 a4 x5 i3 a3)
        (apg26-unchanged-p
         havoc-start havoc-length a4 i1 x3)
        (apg26-a1-separated-t3-closed-range-p
         a1 a4 i1 x1)
        (apg26-t3-closed-range-separated-from-array-p
         a7 a4 i1 x1)
        (apg26-t3-closed-range-addresses-distinct-p
         a4 i1 x1)
        (apg26-t3-closed-range-addresses-separated-p
         a4 i1 x1)
        (apg26-a1-separated-a5-closed-range-p
         a1 a4 x5 x4 havoc-start havoc-length)
        (apg26-a5-closed-range-separated-from-array-p
         a7 a4 i1 (+ i i1 i2 i3)
         havoc-start havoc-length))
       (apg26-p-linked-n-p
        :updated havoc-start havoc-length
        update-address a8
        a8 a4 x3 (+ 1 i3) a3))))))

(value-triple :itpeval-statement-checked)

:q
