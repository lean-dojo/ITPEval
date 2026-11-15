;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/array_push_Why3_ide_VCarray_push_loop_inv_LeftLinked_preserved_part2_goal24:
;; preservation of the left linked-list loop invariant after a havoced
;; pointer-array cell is updated during array push. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun apg24-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun apg24-address-base (address)
  (car address))

(defun apg24-address-offset (address)
  (cdr address))

(defun apg24-shift (address amount)
  (cons
   (apg24-address-base address)
   (+ (apg24-address-offset address) amount)))

;; These conservative function symbols represent the universally arbitrary
;; source functions t_2, t_3, and t, together with the fixed arbitrary region
;; and linked symbols from the memory theory.

(defstub apg24-t2 (address) t)
(defstub apg24-t3 (address) t)
(defstub apg24-malloc (index) t)
(defstub apg24-region (base) t)
(defstub apg24-linked-op () t)

(defun-sk apg24-pointer-functions-p ()
  (forall (address)
    (implies
     (apg24-address-p address)
     (and
      (apg24-address-p (apg24-t2 address))
      (apg24-address-p (apg24-t3 address))))))

(defun-sk apg24-malloc-function-p ()
  (forall (index)
    (implies
     (integerp index)
     (integerp (apg24-malloc index)))))

(defun-sk apg24-region-function-p ()
  (forall (base)
    (implies
     (integerp base)
     (integerp (apg24-region base)))))

(defun apg24-linked-p ()
  (if (apg24-linked-op) t nil))

(defun apg24-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun apg24-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (apg24-address-base left)
     (apg24-address-base right)))
   (<=
    (+ (apg24-address-offset right) right-length)
    (apg24-address-offset left))
   (<=
    (+ (apg24-address-offset left) left-length)
    (apg24-address-offset right))))

(defun apg24-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (apg24-address-base address))
    (<= 0 (apg24-address-offset address))
    (<=
     (+ (apg24-address-offset address) length)
     (apg24-malloc (apg24-address-base address))))))

;; HAVOC is the source memory-theory operation: inside the possibly modified
;; interval it reads t_2, and at every separated address it reads t_3.

(defun apg24-havoc-read
    (havoc-start havoc-length address)
  (if
      (apg24-separated-p address 1 havoc-start havoc-length)
      (apg24-t3 address)
    (apg24-t2 address)))

;; UPDATED-READ is the exact single functional update of A5.

(defun apg24-updated-read
    (havoc-start havoc-length update-address update-value address)
  (if (equal address update-address)
      update-value
    (apg24-havoc-read havoc-start havoc-length address)))

(defun apg24-mptr-read
    (memory-kind havoc-start havoc-length
                 update-address update-value address)
  (cond
   ((equal memory-kind :t3)
    (apg24-t3 address))
   ((equal memory-kind :a5)
    (apg24-havoc-read havoc-start havoc-length address))
   ((equal memory-kind :updated)
    (apg24-updated-read
     havoc-start havoc-length
     update-address update-value address))
   (t nil)))

;; This recursion is equivalent to the source inductive p_linked_n relation:
;; n = 0 is exactly its bound constructor, while n > 0 is exactly its cons
;; constructor followed by the unique recursive predecessor at n - 1.

(defun apg24-p-linked-n-p
    (memory-kind havoc-start havoc-length
                 update-address update-value
                 root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (member-eq memory-kind '(:t3 :a5 :updated))
   (apg24-address-p root)
   (apg24-address-p array)
   (integerp index)
   (integerp n)
   (apg24-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (apg24-mptr-read
        memory-kind havoc-start havoc-length
        update-address update-value
        (apg24-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (apg24-valid-rw-p root 4)
      (apg24-p-linked-n-p
       memory-kind havoc-start havoc-length
       update-address update-value
       (apg24-mptr-read
        memory-kind havoc-start havoc-length
        update-address update-value
        (apg24-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

(defun-sk apg24-framed-p ()
  (forall (address)
    (implies
     (apg24-address-p address)
     (<=
      (apg24-region
       (apg24-address-base (apg24-t3 address)))
      0))))

(defun-sk apg24-array-swipe-right-p
    (havoc-start havoc-length array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (equal
      (apg24-t3 (apg24-shift array (- index 1)))
      (apg24-havoc-read
       havoc-start havoc-length
       (apg24-shift array index))))))

;; In p_unchanged the malloc function and real-valued memory are identical on
;; both sides. After unfolding load_s1_list and eqs1_list, the real equalities
;; follow from the first address equality. The next-pointer equality and
;; valid_rw implication are retained explicitly.

(defun-sk apg24-unchanged-p
    (havoc-start havoc-length array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (let*
         ((slot (apg24-shift array index))
          (left-address
           (apg24-havoc-read
            havoc-start havoc-length slot))
          (right-address (apg24-t3 slot)))
       (and
        (equal left-address right-address)
        (equal
         (apg24-t3 (apg24-shift right-address 0))
         (apg24-havoc-read
          havoc-start havoc-length
          (apg24-shift left-address 0)))
        (implies
         (apg24-valid-rw-p right-address 4)
         (apg24-valid-rw-p left-address 4)))))))

(defun-sk apg24-a1-separated-t3-range-p
    (a1 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (apg24-separated-p
      a1 1
      (apg24-t3 (apg24-shift array index))
      4))))

(defun-sk apg24-t3-range-separated-from-array-p
    (array-base array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (apg24-separated-p
      (apg24-t3 (apg24-shift array index))
      4 array-base 2147483646))))

(defun-sk apg24-t3-range-addresses-distinct-p
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
       (apg24-t3 (apg24-shift array left-index))
       (apg24-t3 (apg24-shift array right-index)))))))

(defun-sk apg24-t3-range-addresses-separated-p
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
     (apg24-separated-p
      (apg24-t3 (apg24-shift array left-index))
      4
      (apg24-t3 (apg24-shift array right-index))
      4))))

(defun-sk apg24-a1-separated-a5-closed-range-p
    (a1 array lower upper havoc-start havoc-length)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (<= index upper))
     (apg24-separated-p
      a1 1
      (apg24-havoc-read
       havoc-start havoc-length
       (apg24-shift array index))
      4))))

(defun-sk apg24-a5-range-separated-from-array-p
    (array-base array lower upper havoc-start havoc-length)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (apg24-separated-p
      (apg24-havoc-read
       havoc-start havoc-length
       (apg24-shift array index))
      4 array-base 2147483646))))

(defun-sk
    ntp4vc-array-push-loop-inv-leftlinked-preserved-part2-goal24-statement ()
  (forall
   (i3 a4 i2 i1 a1 i a a3 a2)
   (implies
    (and
     (apg24-pointer-functions-p)
     (apg24-malloc-function-p)
     (apg24-region-function-p)
     (integerp i3)
     (apg24-address-p a4)
     (integerp i2)
     (integerp i1)
     (apg24-address-p a1)
     (integerp i)
     (apg24-address-p a)
     (apg24-address-p a3)
     (apg24-address-p a2))
    (let*
        ((x (+ 1 i3))
         (havoc-start (apg24-shift a4 (+ 1 i2)))
         (havoc-length i1)
         (a6 (apg24-t3 a1))
         (x1 (+ i1 i2))
         (x2 (+ i2 i3))
         (x3 (+ 1 i2 i3))
         (a7 (apg24-shift a4 0))
         (x4 (+ 2 i2 i3))
         (a8
          (apg24-havoc-read
           havoc-start havoc-length
           (apg24-shift a4 x2)))
         (update-address (apg24-shift a4 x3)))
      (implies
       (and
        (not (equal i1 0))
        (not (equal i3 0))
        (equal (equal x i1) (equal i 0))
        (equal (<= (+ 2 i3) i1) (equal i 1))
        (equal
         (apg24-havoc-read havoc-start havoc-length a1)
         a6)
        (<= 0 i3)
        (< i3 i1)
        (<= (apg24-region (apg24-address-base a)) 0)
        (<= (apg24-region (apg24-address-base a1)) 0)
        (<= (apg24-region (apg24-address-base a3)) 0)
        (<= (apg24-region (apg24-address-base a4)) 0)
        (<= -1 i3)
        (<= x1 2147483645)
        (apg24-framed-p)
        (apg24-linked-p)
        (apg24-is-sint32-p i)
        (apg24-is-sint32-p i1)
        (apg24-is-sint32-p i2)
        (apg24-valid-rw-p a1 1)
        (apg24-is-sint32-p x1)
        (apg24-is-sint32-p x2)
        (apg24-is-sint32-p x3)
        (apg24-valid-rw-p a7 2147483646)
        (apg24-separated-p a1 1 a7 2147483646)
        (apg24-separated-p a6 4 a7 2147483646)
        (apg24-p-linked-n-p
         :t3 havoc-start havoc-length nil nil
         a a4 i2 i1 a3)
        (apg24-array-swipe-right-p
         havoc-start havoc-length
         a4 x4 (+ 1 i1 i2))
        (apg24-p-linked-n-p
         :a5 havoc-start havoc-length nil nil
         a a4 i2 x a2)
        (apg24-p-linked-n-p
         :a5 havoc-start havoc-length nil nil
         a2 a4 x4 (- (- i1 1) i3) a3)
        (apg24-unchanged-p
         havoc-start havoc-length a4 i2 x3)
        (apg24-a1-separated-t3-range-p
         a1 a4 i2 x1)
        (apg24-t3-range-separated-from-array-p
         a7 a4 i2 x1)
        (apg24-t3-range-addresses-distinct-p
         a4 i2 x1)
        (apg24-t3-range-addresses-separated-p
         a4 i2 x1)
        (apg24-a1-separated-a5-closed-range-p
         a1 a4 x4 x1 havoc-start havoc-length)
        (apg24-a5-range-separated-from-array-p
         a7 a4 i2 (+ i i1 i2)
         havoc-start havoc-length))
       (apg24-p-linked-n-p
        :updated havoc-start havoc-length
        update-address a8
        a a4 i2 i3 a8))))))

(value-triple :itpeval-statement-checked)

:q
