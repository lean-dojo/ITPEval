;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/list_tail_Why3_ide_VClist_tail_loop_inv_3_preserved_goal6:
;; preservation of an inductively defined linked-list segment invariant as
;; the list-tail loop advances by one node. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun ltg6-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun ltg6-address-base (address)
  (car address))

(defun ltg6-address-offset (address)
  (cdr address))

(defun ltg6-shift (address amount)
  (cons
   (ltg6-address-base address)
   (+ (ltg6-address-offset address) amount)))

(defun ltg6-null-address ()
  (cons 0 0))

;; These conservative symbols represent the universally arbitrary source
;; pointer function t_1, integer memory-size function t, region operation,
;; and the linked proposition specialized to t.

(defstub ltg6-t1 (address) t)
(defstub ltg6-t (index) t)
(defstub ltg6-region (base) t)
(defstub ltg6-linked-op () t)

(defun-sk ltg6-function-types-p ()
  (forall (address index base)
    (implies
     (and
      (ltg6-address-p address)
      (integerp index)
      (integerp base))
     (and
      (ltg6-address-p (ltg6-t1 address))
      (integerp (ltg6-t index))
      (integerp (ltg6-region base))))))

(defun ltg6-linked-p ()
  (if (ltg6-linked-op) t nil))

(defun ltg6-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun ltg6-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (ltg6-address-base address))
    (<= 0 (ltg6-address-offset address))
    (<=
     (+ (ltg6-address-offset address) length)
     (ltg6-t (ltg6-address-base address))))))

;; This recursion is equivalent to the source inductive p_linked_n relation:
;; n = 0 is exactly its bound constructor, while n > 0 is exactly its cons
;; constructor followed by the unique recursive predecessor at n - 1.

(defun ltg6-p-linked-n-p (root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (ltg6-address-p root)
   (ltg6-address-p array)
   (integerp index)
   (integerp n)
   (ltg6-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (ltg6-t1 (ltg6-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (ltg6-valid-rw-p root 4)
      (ltg6-p-linked-n-p
       (ltg6-t1 (ltg6-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

(defun-sk ltg6-framed-p ()
  (forall (address)
    (implies
     (ltg6-address-p address)
     (<=
      (ltg6-region
       (ltg6-address-base (ltg6-t1 address)))
      0))))

(defun-sk
    ntp4vc-list-tail-loop-inv-3-preserved-goal6-statement ()
  (forall
   (a i1 i2 a1 i)
   (implies
    (and
     (ltg6-function-types-p)
     (ltg6-address-p a)
     (integerp i1)
     (integerp i2)
     (ltg6-address-p a1)
     (integerp i))
    (let*
        ((a2 (ltg6-t1 a))
         (x (+ i1 i2))
         (a3 (ltg6-t1 (ltg6-shift a1 x)))
         (a4 (ltg6-t1 (ltg6-shift a3 0)))
         (x1 (+ 1 i2)))
      (implies
       (and
        (not (equal a2 (ltg6-null-address)))
        (not (equal a4 (ltg6-null-address)))
        (<= 0 i2)
        (< i2 i)
        (<= (ltg6-region (ltg6-address-base a)) 0)
        (<= (ltg6-region (ltg6-address-base a1)) 0)
        (ltg6-framed-p)
        (ltg6-linked-p)
        (ltg6-is-sint32-p i)
        (ltg6-is-sint32-p i1)
        (ltg6-is-sint32-p i2)
        (ltg6-valid-rw-p a 1)
        (ltg6-is-sint32-p x1)
        (ltg6-valid-rw-p
         (ltg6-shift a1 0)
         2147483646)
        (ltg6-p-linked-n-p
         a2 a1 i1 i (ltg6-null-address))
        (ltg6-p-linked-n-p
         a2 a1 i1 i2 a3)
        (ltg6-p-linked-n-p
         a3 a1 x (- i i2) (ltg6-null-address)))
       (ltg6-p-linked-n-p
        a2 a1 i1 x1 a4))))))

(value-triple :itpeval-statement-checked)

:q
