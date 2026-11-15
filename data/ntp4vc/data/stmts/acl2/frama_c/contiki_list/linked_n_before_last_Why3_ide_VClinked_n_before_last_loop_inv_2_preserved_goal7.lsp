;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/linked_n_before_last_Why3_ide_VClinked_n_before_last_loop_inv_2_preserved_goal7:
;; preservation of an inductively defined linked-list segment invariant when
;; the before-last loop advances by one array index. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lnblg7-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lnblg7-address-base (address)
  (car address))

(defun lnblg7-address-offset (address)
  (cdr address))

(defun lnblg7-shift (address amount)
  (cons
   (lnblg7-address-base address)
   (+ (lnblg7-address-offset address) amount)))

;; These conservative symbols represent the universally arbitrary source
;; pointer function t_1, integer function t, region operation, and the linked
;; proposition specialized to t.

(defstub lnblg7-t1 (address) t)
(defstub lnblg7-t (index) t)
(defstub lnblg7-region (base) t)
(defstub lnblg7-linked-op () t)

(defun-sk lnblg7-function-types-p ()
  (forall (address index base)
    (implies
     (and
      (lnblg7-address-p address)
      (integerp index)
      (integerp base))
     (and
      (lnblg7-address-p (lnblg7-t1 address))
      (integerp (lnblg7-t index))
      (integerp (lnblg7-region base))))))

(defun lnblg7-linked-p ()
  (if (lnblg7-linked-op) t nil))

(defun lnblg7-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lnblg7-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lnblg7-address-base address))
    (<= 0 (lnblg7-address-offset address))
    (<=
     (+ (lnblg7-address-offset address) length)
     (lnblg7-t (lnblg7-address-base address))))))

;; This recursion is equivalent to the source inductive p_linked_n relation:
;; n = 0 is exactly its bound constructor, while n > 0 is exactly its cons
;; constructor followed by the recursive predecessor at n - 1.

(defun lnblg7-p-linked-n-p (root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (lnblg7-address-p root)
   (lnblg7-address-p array)
   (integerp index)
   (integerp n)
   (lnblg7-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (lnblg7-t1 (lnblg7-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (lnblg7-valid-rw-p root 4)
      (lnblg7-p-linked-n-p
       (lnblg7-t1 (lnblg7-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

(defun-sk lnblg7-framed-p ()
  (forall (address)
    (implies
     (lnblg7-address-p address)
     (<=
      (lnblg7-region
       (lnblg7-address-base (lnblg7-t1 address)))
      0))))

(defun-sk
    ntp4vc-linked-n-before-last-loop-inv-2-preserved-goal7-statement ()
  (forall
   (i1 i i2 a2 a a1)
   (implies
    (and
     (lnblg7-function-types-p)
     (integerp i1)
     (integerp i)
     (integerp i2)
     (lnblg7-address-p a2)
     (lnblg7-address-p a)
     (lnblg7-address-p a1))
    (let*
        ((x (+ 1 i1))
         (x1 (+ i i2))
         (a3 (lnblg7-t1 (lnblg7-shift a2 (+ i i1))))
         (x3 (- (+ i i2) 1)))
      (implies
       (and
        (< 0 i2)
        (<= 0 i)
        (<= 0 i1)
        (<= i2 i1)
        (<= 0 i2)
        (<= (lnblg7-region (lnblg7-address-base a)) 0)
        (<= (lnblg7-region (lnblg7-address-base a1)) 0)
        (<= (lnblg7-region (lnblg7-address-base a2)) 0)
        (lnblg7-framed-p)
        (lnblg7-linked-p)
        (lnblg7-is-sint32-p i)
        (lnblg7-is-sint32-p i1)
        (lnblg7-is-sint32-p i2)
        (lnblg7-is-sint32-p (- i2 1))
        (lnblg7-is-sint32-p x)
        (lnblg7-valid-rw-p
         (lnblg7-shift a2 0)
         2147483646)
        (lnblg7-p-linked-n-p
         a a2 i x a1)
        (lnblg7-p-linked-n-p
         (lnblg7-t1 (lnblg7-shift a2 x1))
         a2 x1 (- i1 i2) a3))
       (lnblg7-p-linked-n-p
        (lnblg7-t1 (lnblg7-shift a2 x3))
        a2 x3 (- (+ 1 i1) i2) a3))))))

(value-triple :itpeval-statement-checked)

:q
