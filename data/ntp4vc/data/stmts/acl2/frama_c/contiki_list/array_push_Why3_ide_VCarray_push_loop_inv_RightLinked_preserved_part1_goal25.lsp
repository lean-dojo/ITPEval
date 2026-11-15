;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/array_push_Why3_ide_VCarray_push_loop_inv_RightLinked_preserved_part1_goal25:
;; preservation of the right linked-list loop invariant after a havoced
;; pointer-array cell is updated during array push. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun apg25-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun apg25-address-base (address)
  (car address))

(defun apg25-address-offset (address)
  (cdr address))

(defun apg25-shift (address amount)
  (cons
   (apg25-address-base address)
   (+ (apg25-address-offset address) amount)))

;; These conservative function symbols represent the universally arbitrary
;; source functions t_2, t_3, and t, together with the fixed arbitrary region
;; and linked symbols from the memory theory.

(defstub apg25-t2 (address) t)
(defstub apg25-t3 (address) t)
(defstub apg25-malloc (index) t)
(defstub apg25-region (base) t)
(defstub apg25-linked-op () t)

(defun-sk apg25-pointer-functions-p ()
  (forall (address)
    (implies
     (apg25-address-p address)
     (and
      (apg25-address-p (apg25-t2 address))
      (apg25-address-p (apg25-t3 address))))))

(defun-sk apg25-malloc-function-p ()
  (forall (index)
    (implies
     (integerp index)
     (integerp (apg25-malloc index)))))

(defun-sk apg25-region-function-p ()
  (forall (base)
    (implies
     (integerp base)
     (integerp (apg25-region base)))))

(defun apg25-linked-p ()
  (if (apg25-linked-op) t nil))

(defun apg25-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun apg25-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (apg25-address-base left)
     (apg25-address-base right)))
   (<=
    (+ (apg25-address-offset right) right-length)
    (apg25-address-offset left))
   (<=
    (+ (apg25-address-offset left) left-length)
    (apg25-address-offset right))))

(defun apg25-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (apg25-address-base address))
    (<= 0 (apg25-address-offset address))
    (<=
     (+ (apg25-address-offset address) length)
     (apg25-malloc (apg25-address-base address))))))

;; HAVOC is the source memory-theory operation: inside the possibly modified
;; interval it reads t_2, and at every separated address it reads t_3.

(defun apg25-havoc-read
    (havoc-start havoc-length address)
  (if
      (apg25-separated-p address 1 havoc-start havoc-length)
      (apg25-t3 address)
    (apg25-t2 address)))

;; UPDATED-READ is the exact single functional update of A5.

(defun apg25-updated-read
    (havoc-start havoc-length update-address update-value address)
  (if (equal address update-address)
      update-value
    (apg25-havoc-read havoc-start havoc-length address)))

(defun apg25-mptr-read
    (memory-kind havoc-start havoc-length
                 update-address update-value address)
  (cond
   ((equal memory-kind :t3)
    (apg25-t3 address))
   ((equal memory-kind :a6)
    (apg25-havoc-read havoc-start havoc-length address))
   ((equal memory-kind :updated)
    (apg25-updated-read
     havoc-start havoc-length
     update-address update-value address))
   (t nil)))

;; This recursion is equivalent to the source inductive p_linked_n relation:
;; n = 0 is exactly its bound constructor, while n > 0 is exactly its cons
;; constructor followed by the unique recursive predecessor at n - 1.

(defun apg25-p-linked-n-p
    (memory-kind havoc-start havoc-length
                 update-address update-value
                 root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (member-eq memory-kind '(:t3 :a6 :updated))
   (apg25-address-p root)
   (apg25-address-p array)
   (integerp index)
   (integerp n)
   (apg25-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (apg25-mptr-read
        memory-kind havoc-start havoc-length
        update-address update-value
        (apg25-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (apg25-valid-rw-p root 4)
      (apg25-p-linked-n-p
       memory-kind havoc-start havoc-length
       update-address update-value
       (apg25-mptr-read
        memory-kind havoc-start havoc-length
        update-address update-value
        (apg25-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

(defun-sk apg25-framed-p ()
  (forall (address)
    (implies
     (apg25-address-p address)
     (<=
      (apg25-region
       (apg25-address-base (apg25-t3 address)))
      0))))

(defun-sk apg25-array-swipe-right-p
    (havoc-start havoc-length array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (equal
      (apg25-t3 (apg25-shift array (- index 1)))
      (apg25-havoc-read
       havoc-start havoc-length
       (apg25-shift array index))))))

;; In p_unchanged the malloc function and real-valued memory are identical on
;; both sides. After unfolding load_s1_list and eqs1_list, the real equalities
;; follow from the first address equality. The next-pointer equality and
;; valid_rw implication are retained explicitly.

(defun-sk apg25-unchanged-p
    (havoc-start havoc-length array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (let*
         ((slot (apg25-shift array index))
          (left-address
           (apg25-havoc-read
            havoc-start havoc-length slot))
          (right-address (apg25-t3 slot)))
       (and
        (equal left-address right-address)
        (equal
         (apg25-t3 (apg25-shift right-address 0))
         (apg25-havoc-read
          havoc-start havoc-length
          (apg25-shift left-address 0)))
        (implies
         (apg25-valid-rw-p right-address 4)
         (apg25-valid-rw-p left-address 4)))))))

(defun-sk apg25-a-separated-t3-range-p
    (a array i1 x1)
  (forall (index)
    (implies
     (and
      (integerp index)
      (< index x1)
      (<= i1 (+ 1 index)))
     (apg25-separated-p
      a 1
      (apg25-t3 (apg25-shift array index))
      4))))

(defun-sk apg25-t3-range-separated-from-array-p
    (array-base array i1 x1)
  (forall (index)
    (implies
     (and
      (integerp index)
      (< index x1)
      (<= i1 (+ 1 index)))
     (apg25-separated-p
      (apg25-t3 (apg25-shift array index))
      4 array-base 2147483646))))

(defun-sk apg25-t3-range-addresses-distinct-p
    (array i1 x1)
  (forall (left-index right-index)
    (implies
     (and
      (integerp left-index)
      (integerp right-index)
      (not (equal left-index right-index))
      (< right-index x1)
      (< left-index x1)
      (<= i1 (+ 1 right-index))
      (<= i1 (+ 1 left-index)))
     (not
      (equal
       (apg25-t3 (apg25-shift array left-index))
       (apg25-t3 (apg25-shift array right-index)))))))

(defun-sk apg25-a-separated-a6-closed-range-p
    (a array i1 x1 havoc-start havoc-length)
  (forall (index)
    (implies
     (and
      (integerp index)
      (< i1 index)
      (<= index x1))
     (apg25-separated-p
      a 1
      (apg25-havoc-read
       havoc-start havoc-length
       (apg25-shift array index))
      4))))

(defun-sk apg25-a6-range-separated-from-array-p
    (array-base array i i1 i2 havoc-start havoc-length)
  (forall (index)
    (implies
     (and
      (integerp index)
      (< index (+ i i1 i2))
      (<= i1 (+ 1 index)))
     (apg25-separated-p
      (apg25-havoc-read
       havoc-start havoc-length
       (apg25-shift array index))
      4 array-base 2147483646))))

(defun-sk apg25-t3-range-addresses-separated-p
    (array i1 x1)
  (forall (left-index right-index)
    (implies
     (and
      (integerp left-index)
      (integerp right-index)
      (not (equal left-index right-index))
      (< right-index x1)
      (< left-index x1)
      (<= i1 (+ 1 right-index))
      (<= i1 (+ 1 left-index)))
     (apg25-separated-p
      (apg25-t3 (apg25-shift array left-index))
      4
      (apg25-t3 (apg25-shift array right-index))
      4))))

(defun-sk
    ntp4vc-array-push-loop-inv-rightlinked-preserved-part1-goal25-statement ()
  (forall
   (a4 i1 i2 a i a2 a3 a1)
   (implies
    (and
     (apg25-pointer-functions-p)
     (apg25-malloc-function-p)
     (apg25-region-function-p)
     (apg25-address-p a4)
     (integerp i1)
     (integerp i2)
     (apg25-address-p a)
     (integerp i)
     (apg25-address-p a2)
     (apg25-address-p a3)
     (apg25-address-p a1))
    (let*
        ((havoc-start (apg25-shift a4 i1))
         (havoc-length (+ 1 i2))
         (a7 (apg25-t3 a))
         (x1 (+ i1 i2))
         (x2 (- i1 1))
         (a8 (apg25-shift a4 0))
         (x3 (+ 1 i1))
         (update-address havoc-start)
         (update-value
          (apg25-havoc-read
           havoc-start havoc-length
           (apg25-shift a4 x2))))
      (implies
       (and
        (not (equal i2 -1))
        (equal (equal i2 0) (equal i 0))
        (equal (< 0 i2) (equal i 1))
        (equal
         (apg25-havoc-read havoc-start havoc-length a)
         a7)
        (<= 0 i2)
        (<= (apg25-region (apg25-address-base a)) 0)
        (<= (apg25-region (apg25-address-base a2)) 0)
        (<= (apg25-region (apg25-address-base a3)) 0)
        (<= (apg25-region (apg25-address-base a4)) 0)
        (<= x1 2147483645)
        (apg25-framed-p)
        (apg25-linked-p)
        (apg25-is-sint32-p i)
        (apg25-is-sint32-p i1)
        (apg25-valid-rw-p a 1)
        (apg25-is-sint32-p x2)
        (apg25-is-sint32-p havoc-length)
        (apg25-is-sint32-p x1)
        (apg25-valid-rw-p a8 2147483646)
        (apg25-separated-p a 1 a8 2147483646)
        (apg25-separated-p a7 4 a8 2147483646)
        (apg25-p-linked-n-p
         :t3 havoc-start havoc-length nil nil
         a2 a4 x2 havoc-length a3)
        (apg25-array-swipe-right-p
         havoc-start havoc-length
         a4 x3 (+ 1 i1 i2))
        (apg25-p-linked-n-p
         :a6 havoc-start havoc-length nil nil
         a1 a4 x3 i2 a3)
        (apg25-p-linked-n-p
         :a6 havoc-start havoc-length nil nil
         a2 a4 x2 1 a1)
        (apg25-unchanged-p
         havoc-start havoc-length a4 x2 i1)
        (apg25-a-separated-t3-range-p
         a a4 i1 x1)
        (apg25-t3-range-separated-from-array-p
         a8 a4 i1 x1)
        (apg25-t3-range-addresses-distinct-p
         a4 i1 x1)
        (apg25-a-separated-a6-closed-range-p
         a a4 i1 x1 havoc-start havoc-length)
        (apg25-a6-range-separated-from-array-p
         a8 a4 i i1 i2 havoc-start havoc-length)
        (apg25-t3-range-addresses-separated-p
         a4 i1 x1))
       (apg25-p-linked-n-p
        :updated havoc-start havoc-length
        update-address update-value
        a2 a4 i1 havoc-length a3))))))

(value-triple :itpeval-statement-checked)

:q
