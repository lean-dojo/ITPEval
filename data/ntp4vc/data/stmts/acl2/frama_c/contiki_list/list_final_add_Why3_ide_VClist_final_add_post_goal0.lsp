;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/list_final_add_Why3_ide_VClist_final_add_post_goal0:
;; preservation and extension of an inductively defined linked-list segment
;; after two pointer-memory updates under the stated validity, framing,
;; separation, distinctness, and range conditions. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lfag0-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lfag0-address-base (address)
  (car address))

(defun lfag0-address-offset (address)
  (cdr address))

(defun lfag0-shift (address amount)
  (cons
   (lfag0-address-base address)
   (+ (lfag0-address-offset address) amount)))

(defun lfag0-null-address ()
  (cons 0 0))

;; These conservative symbols represent the universally arbitrary source
;; pointer function t_1, allocation function t, region function, and linked
;; proposition specialized to t.

(defstub lfag0-t1 (address) t)
(defstub lfag0-malloc (index) t)
(defstub lfag0-region (base) t)
(defstub lfag0-linked-op () t)

(defun-sk lfag0-function-types-p ()
  (forall (address index base)
    (implies
     (and
      (lfag0-address-p address)
      (integerp index)
      (integerp base))
     (and
      (lfag0-address-p (lfag0-t1 address))
      (integerp (lfag0-malloc index))
      (integerp (lfag0-region base))))))

(defun lfag0-linked-p ()
  (if (lfag0-linked-op) t nil))

(defun lfag0-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lfag0-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (lfag0-address-base left)
     (lfag0-address-base right)))
   (<=
    (+ (lfag0-address-offset right) right-length)
    (lfag0-address-offset left))
   (<=
    (+ (lfag0-address-offset left) left-length)
    (lfag0-address-offset right))))

(defun lfag0-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lfag0-address-base address))
    (<= 0 (lfag0-address-offset address))
    (<=
     (+ (lfag0-address-offset address) length)
     (lfag0-malloc (lfag0-address-base address))))))

(defun-sk lfag0-framed-p ()
  (forall (address)
    (implies
     (lfag0-address-p address)
     (<=
      (lfag0-region
       (lfag0-address-base (lfag0-t1 address)))
      0))))

;; M is Function.update (Function.update t_1 (shift a_3 x) a_1)
;; (shift a_2 0) a_1. The outer update has precedence.

(defun lfag0-pointer-read
    (memory-kind a1 a2 a3 x address)
  (if (equal memory-kind :updated)
      (cond
       ((equal address (lfag0-shift a2 0)) a1)
       ((equal address (lfag0-shift a3 x)) a1)
       (t (lfag0-t1 address)))
    (lfag0-t1 address)))

;; This recursion is equivalent to the source inductive p_linked_n relation:
;; n = 0 is its bound constructor, while n > 0 is its cons constructor
;; followed by the unique recursive predecessor at n - 1.

(defun lfag0-p-linked-n-p
    (memory-kind a1 a2 a3 x root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (member-eq memory-kind '(:base :updated))
   (lfag0-address-p root)
   (lfag0-address-p array)
   (integerp index)
   (integerp n)
   (lfag0-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (lfag0-pointer-read
        memory-kind a1 a2 a3 x
        (lfag0-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (lfag0-valid-rw-p root 4)
      (lfag0-p-linked-n-p
       memory-kind a1 a2 a3 x
       (lfag0-pointer-read
        memory-kind a1 a2 a3 x
        (lfag0-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

(defun-sk lfag0-a-separated-range-p
    (a a3 lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lfag0-separated-p
      a 1
      (lfag0-t1 (lfag0-shift a3 index))
      4))))

(defun-sk lfag0-a1-separated-range-p
    (a1 a3 lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lfag0-separated-p
      a1 4
      (lfag0-t1 (lfag0-shift a3 index))
      4))))

(defun-sk lfag0-range-separated-from-array-p
    (a3 lower upper)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= lower index)
      (< index upper))
     (lfag0-separated-p
      (lfag0-t1 (lfag0-shift a3 index))
      4
      (lfag0-shift a3 0)
      2147483646))))

(defun-sk lfag0-range-distinct-p
    (a3 lower upper)
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
       (lfag0-t1 (lfag0-shift a3 left-index))
       (lfag0-t1 (lfag0-shift a3 right-index)))))))

(defun-sk lfag0-range-separated-p
    (a3 lower upper)
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
     (lfag0-separated-p
      (lfag0-t1 (lfag0-shift a3 left-index))
      4
      (lfag0-t1 (lfag0-shift a3 right-index))
      4))))

(defun-sk ntp4vc-list-final-add-post-goal0-statement ()
  (forall
   (a1 i i1 a3 a a2)
   (implies
    (and
     (lfag0-function-types-p)
     (lfag0-address-p a1)
     (integerp i)
     (integerp i1)
     (lfag0-address-p a3)
     (lfag0-address-p a)
     (lfag0-address-p a2))
    (let*
        ((a4 (lfag0-t1 (lfag0-shift a1 0)))
         (x (+ i i1))
         (a5 (lfag0-shift a3 0))
         (a6 (lfag0-t1 a))
         (a7 (lfag0-shift a2 0))
         (m-a
          (lfag0-pointer-read
           :updated a1 a2 a3 x a)))
      (implies
       (and
        (equal a4 (lfag0-null-address))
        (< 0 x)
        (<= (lfag0-region (lfag0-address-base a)) 0)
        (<= (lfag0-region (lfag0-address-base a1)) 0)
        (<= (lfag0-region (lfag0-address-base a2)) 0)
        (<= (lfag0-region (lfag0-address-base a3)) 0)
        (<= x 2147483645)
        (lfag0-framed-p)
        (lfag0-linked-p)
        (lfag0-is-sint32-p i)
        (lfag0-is-sint32-p i1)
        (lfag0-valid-rw-p a 1)
        (lfag0-valid-rw-p a1 4)
        (lfag0-valid-rw-p a2 4)
        (lfag0-separated-p a 1 a1 4)
        (lfag0-separated-p a 1 a2 4)
        (lfag0-separated-p a2 4 a1 4)
        (lfag0-valid-rw-p a5 2147483646)
        (lfag0-separated-p a 1 a5 2147483646)
        (lfag0-separated-p a1 4 a5 2147483646)
        (lfag0-separated-p a6 4 a5 2147483646)
        (lfag0-p-linked-n-p
         :base a1 a2 a3 x
         a6 a3 i1 (- i 1) a2)
        (lfag0-p-linked-n-p
         :base a1 a2 a3 x
         a2 a3 (- (+ i i1) 1) 1
         (lfag0-t1 a7))
        (lfag0-a-separated-range-p a a3 i1 x)
        (lfag0-a1-separated-range-p a1 a3 i1 x)
        (lfag0-range-separated-from-array-p a3 i1 x)
        (lfag0-range-distinct-p a3 i1 x)
        (lfag0-range-separated-p a3 i1 x))
       (lfag0-p-linked-n-p
        :updated a1 a2 a3 x
        m-a a3 i1 (+ 1 i) a4))))))

(value-triple :itpeval-statement-checked)

:q
