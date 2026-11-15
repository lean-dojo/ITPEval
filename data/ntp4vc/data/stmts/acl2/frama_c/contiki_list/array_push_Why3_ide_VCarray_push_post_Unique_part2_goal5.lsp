;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/array_push_Why3_ide_VCarray_push_post_Unique_part2_goal5:
;; distinctness of two differently indexed entries after a null update to a
;; havoced pointer array during array push. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun apug5-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun apug5-address-base (address)
  (car address))

(defun apug5-address-offset (address)
  (cdr address))

(defun apug5-shift (address amount)
  (cons
   (apug5-address-base address)
   (+ (apug5-address-offset address) amount)))

;; These conservative symbols represent the universally arbitrary source
;; functions t_2, t_3, and t, and the fixed region and linked symbols.

(defstub apug5-t2 (address) t)
(defstub apug5-t3 (address) t)
(defstub apug5-malloc (index) t)
(defstub apug5-region (base) t)
(defstub apug5-linked-op () t)

(defun-sk apug5-pointer-functions-p ()
  (forall (address)
    (implies
     (apug5-address-p address)
     (and
      (apug5-address-p (apug5-t2 address))
      (apug5-address-p (apug5-t3 address))))))

(defun-sk apug5-malloc-function-p ()
  (forall (index)
    (implies
     (integerp index)
     (integerp (apug5-malloc index)))))

(defun-sk apug5-region-function-p ()
  (forall (base)
    (implies
     (integerp base)
     (integerp (apug5-region base)))))

(defun apug5-linked-p ()
  (if (apug5-linked-op) t nil))

(defun apug5-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun apug5-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (apug5-address-base left)
     (apug5-address-base right)))
   (<=
    (+ (apug5-address-offset right) right-length)
    (apug5-address-offset left))
   (<=
    (+ (apug5-address-offset left) left-length)
    (apug5-address-offset right))))

(defun apug5-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (apug5-address-base address))
    (<= 0 (apug5-address-offset address))
    (<=
     (+ (apug5-address-offset address) length)
     (apug5-malloc (apug5-address-base address))))))

;; HAVOC-READ is the source memory-theory havoc operation, characterized by
;; its access equation.

(defun apug5-havoc-read
    (havoc-start havoc-length address)
  (if
      (apug5-separated-p address 1 havoc-start havoc-length)
      (apug5-t3 address)
    (apug5-t2 address)))

;; UPDATED-READ is the exact functional update of the second havoced memory
;; at the designated array slot with the null address.

(defun apug5-updated-read
    (havoc-start havoc-length update-address address)
  (if (equal address update-address)
      (cons 0 0)
    (apug5-havoc-read havoc-start havoc-length address)))

(defun apug5-mptr-read
    (memory-kind havoc-start havoc-length address)
  (cond
   ((equal memory-kind :t3)
    (apug5-t3 address))
   ((equal memory-kind :a5)
    (apug5-havoc-read havoc-start havoc-length address))
   (t nil)))

;; This recursion is equivalent to the source inductive p_linked_n relation:
;; n = 0 is its bound constructor, while n > 0 is its cons constructor
;; followed by the unique recursive predecessor at n - 1.

(defun apug5-p-linked-n-p
    (memory-kind havoc-start havoc-length
                 root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (member-eq memory-kind '(:t3 :a5))
   (apug5-address-p root)
   (apug5-address-p array)
   (integerp index)
   (integerp n)
   (apug5-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (apug5-mptr-read
        memory-kind havoc-start havoc-length
        (apug5-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (apug5-valid-rw-p root 4)
      (apug5-p-linked-n-p
       memory-kind havoc-start havoc-length
       (apug5-mptr-read
        memory-kind havoc-start havoc-length
        (apug5-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

(defun-sk apug5-framed-p ()
  (forall (address)
    (implies
     (apug5-address-p address)
     (<=
      (apug5-region
       (apug5-address-base (apug5-t3 address)))
      0))))

(defun-sk apug5-array-swipe-right-p
    (havoc-start havoc-length array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (equal
      (apug5-t3 (apug5-shift array (- index 1)))
      (apug5-havoc-read
       havoc-start havoc-length
       (apug5-shift array index))))))

;; The source p_unchanged uses the same malloc function and real-valued memory
;; on both sides. Unfolding load_s1_list and eqs1_list makes the real fields
;; equal once the selected addresses are equal; the next-pointer equality and
;; valid_rw implication below are precisely the remaining conjuncts.

(defun-sk apug5-unchanged-p
    (havoc-start havoc-length array down up)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= down index)
      (< index up))
     (let*
         ((slot (apug5-shift array index))
          (left-address
           (apug5-havoc-read
            havoc-start havoc-length slot))
          (right-address (apug5-t3 slot)))
       (and
        (equal left-address right-address)
        (equal
         (apug5-t3 (apug5-shift right-address 0))
         (apug5-havoc-read
          havoc-start havoc-length
          (apug5-shift left-address 0)))
        (implies
         (apug5-valid-rw-p right-address 4)
         (apug5-valid-rw-p left-address 4)))))))

(defun-sk apug5-a1-separated-t3-range-p
    (a1 array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (apug5-separated-p
      a1 1
      (apug5-t3 (apug5-shift array index))
      4))))

(defun-sk apug5-t3-range-separated-from-array-p
    (array-base array lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (apug5-separated-p
      (apug5-t3 (apug5-shift array index))
      4 array-base 2147483646))))

(defun-sk apug5-t3-range-addresses-distinct-p
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
       (apug5-t3 (apug5-shift array left-index))
       (apug5-t3 (apug5-shift array right-index)))))))

(defun-sk apug5-t3-range-addresses-separated-p
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
     (apug5-separated-p
      (apug5-t3 (apug5-shift array left-index))
      4
      (apug5-t3 (apug5-shift array right-index))
      4))))

(defun-sk apug5-a1-separated-a5-open-closed-range-p
    (a1 array lower upper havoc-start havoc-length)
  (forall (index)
    (implies
     (and
      (integerp index)
      (< lower index)
      (<= index upper))
     (apug5-separated-p
      a1 1
      (apug5-havoc-read
       havoc-start havoc-length
       (apug5-shift array index))
      4))))

(defun-sk apug5-a5-range-separated-from-array-p
    (array-base array lower upper havoc-start havoc-length)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (apug5-separated-p
      (apug5-havoc-read
       havoc-start havoc-length
       (apug5-shift array index))
      4 array-base 2147483646))))

(defun-sk
    ntp4vc-array-push-post-unique-part2-goal5-statement ()
  (forall
   (i1 i2 a4 a1 i3 i5 i4 i a a3 a2)
   (implies
    (and
     (integerp i1)
     (integerp i2)
     (apug5-address-p a4)
     (apug5-address-p a1)
     (integerp i3)
     (integerp i5)
     (integerp i4)
     (integerp i)
     (apug5-address-p a)
     (apug5-address-p a3)
     (apug5-address-p a2)
     (apug5-pointer-functions-p)
     (apug5-malloc-function-p)
     (apug5-region-function-p))
    (let*
        ((x (+ i1 i2))
         (a5-havoc-start (apug5-shift a4 (+ 1 i2)))
         (a5-havoc-length i1)
         (a6 (apug5-t3 a1))
         (a7 (apug5-shift a4 0))
         (x1 (+ 1 i3))
         (a8-havoc-start (apug5-shift a4 x1))
         (a8-havoc-length i1)
         (a8-update-address (apug5-shift a4 i3)))
      (implies
       (and
        (not (equal i1 0))
        (not (equal i5 i4))
        (equal (equal x i3) (equal i 0))
        (equal (< i3 x) (equal i 1))
        (equal
         (apug5-havoc-read
          a5-havoc-start a5-havoc-length a1)
         a6)
        (<= i3 i2)
        (<= i2 i3)
        (<= i2 i4)
        (<= i2 i5)
        (<= i3 x)
        (<= i4 x)
        (<= i5 x)
        (<= (apug5-region (apug5-address-base a)) 0)
        (<= (apug5-region (apug5-address-base a1)) 0)
        (<= (apug5-region (apug5-address-base a3)) 0)
        (<= (apug5-region (apug5-address-base a4)) 0)
        (<= x 2147483645)
        (apug5-framed-p)
        (apug5-linked-p)
        (apug5-is-sint32-p i)
        (apug5-is-sint32-p i1)
        (apug5-is-sint32-p i2)
        (apug5-is-sint32-p i3)
        (apug5-valid-rw-p a1 1)
        (apug5-is-sint32-p x)
        (apug5-valid-rw-p a7 2147483646)
        (apug5-separated-p a1 1 a7 2147483646)
        (apug5-separated-p a6 4 a7 2147483646)
        (apug5-p-linked-n-p
         :t3 a5-havoc-start a5-havoc-length
         a a4 i2 i1 a3)
        (apug5-array-swipe-right-p
         a5-havoc-start a5-havoc-length
         a4 x1 (+ 1 i1 i2))
        (apug5-p-linked-n-p
         :a5 a5-havoc-start a5-havoc-length
         a a4 i2 (- i3 i2) a2)
        (apug5-p-linked-n-p
         :a5 a5-havoc-start a5-havoc-length
         a2 a4 x1 (- (+ i1 i2) i3) a3)
        (apug5-unchanged-p
         a5-havoc-start a5-havoc-length a4 i2 i3)
        (apug5-a1-separated-t3-range-p a1 a4 i2 x)
        (apug5-t3-range-separated-from-array-p a7 a4 i2 x)
        (apug5-t3-range-addresses-distinct-p a4 i2 x)
        (apug5-t3-range-addresses-separated-p a4 i2 x)
        (apug5-a1-separated-a5-open-closed-range-p
         a1 a4 i3 x a5-havoc-start a5-havoc-length)
        (apug5-a5-range-separated-from-array-p
         a7 a4 i2 (+ i i1 i2)
         a5-havoc-start a5-havoc-length))
       (not
        (equal
         (apug5-updated-read
          a8-havoc-start a8-havoc-length
          a8-update-address
          (apug5-shift a4 i5))
         (apug5-updated-read
          a8-havoc-start a8-havoc-length
          a8-update-address
          (apug5-shift a4 i4)))))))))

(value-triple :itpeval-statement-checked)

:q
