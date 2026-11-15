;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/linked_n_split_segment_Why3_ide_VClinked_n_split_segment_loop_inv_3_preserved_goal10:
;; preservation of an inductively defined linked-list segment invariant while
;; splitting a list segment. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lnssg10-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lnssg10-address-base (address)
  (car address))

(defun lnssg10-address-offset (address)
  (cdr address))

(defun lnssg10-shift (address amount)
  (cons
   (lnssg10-address-base address)
   (+ (lnssg10-address-offset address) amount)))

;; These conservative symbols represent the universally arbitrary source
;; pointer function t_1, integer function t, region operation, and the linked
;; proposition specialized to t.

(defstub lnssg10-t1 (address) t)
(defstub lnssg10-t (index) t)
(defstub lnssg10-region (base) t)
(defstub lnssg10-linked-op () t)

(defun-sk lnssg10-function-types-p ()
  (forall (address index base)
    (implies
     (and
      (lnssg10-address-p address)
      (integerp index)
      (integerp base))
     (and
      (lnssg10-address-p (lnssg10-t1 address))
      (integerp (lnssg10-t index))
      (integerp (lnssg10-region base))))))

(defun lnssg10-linked-p ()
  (if (lnssg10-linked-op) t nil))

(defun lnssg10-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lnssg10-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lnssg10-address-base address))
    (<= 0 (lnssg10-address-offset address))
    (<=
     (+ (lnssg10-address-offset address) length)
     (lnssg10-t (lnssg10-address-base address))))))

;; This recursion is equivalent to the source inductive p_linked_n relation:
;; n = 0 is exactly its bound constructor, while n > 0 is exactly its cons
;; constructor followed by the unique recursive predecessor at n - 1.

(defun lnssg10-p-linked-n-p (root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (lnssg10-address-p root)
   (lnssg10-address-p array)
   (integerp index)
   (integerp n)
   (lnssg10-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (lnssg10-t1 (lnssg10-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (lnssg10-valid-rw-p root 4)
      (lnssg10-p-linked-n-p
       (lnssg10-t1 (lnssg10-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

(defun-sk lnssg10-framed-p ()
  (forall (address)
    (implies
     (lnssg10-address-p address)
     (<=
      (lnssg10-region
       (lnssg10-address-base (lnssg10-t1 address)))
      0))))

(defun-sk
    ntp4vc-linked-n-split-segment-loop-inv-3-preserved-goal10-statement ()
  (forall
   (i i1 i3 a2 i2 a a1)
   (implies
    (and
     (lnssg10-function-types-p)
     (integerp i)
     (integerp i1)
     (integerp i3)
     (lnssg10-address-p a2)
     (integerp i2)
     (lnssg10-address-p a)
     (lnssg10-address-p a1))
    (let*
        ((x (+ i i1))
         (x1 (- i3 1))
         (a3
          (lnssg10-t1
           (lnssg10-shift
            (lnssg10-t1
             (lnssg10-shift a2 (- (+ i2 i3) 1)))
            0))))
      (implies
       (and
        (< 0 i)
        (< i i3)
        (<= 0 i1)
        (<= 0 i2)
        (<= i i3)
        (<= i3 x)
        (<= (lnssg10-region (lnssg10-address-base a)) 0)
        (<= (lnssg10-region (lnssg10-address-base a1)) 0)
        (<= (lnssg10-region (lnssg10-address-base a2)) 0)
        (<=
         (lnssg10-region
          (lnssg10-address-base
           (lnssg10-t1
            (lnssg10-shift
             (lnssg10-t1
              (lnssg10-shift a2 (- (+ i i2) 1)))
             0))))
         0)
        (lnssg10-framed-p)
        (lnssg10-linked-p)
        (lnssg10-is-sint32-p i)
        (lnssg10-is-sint32-p i1)
        (lnssg10-is-sint32-p i2)
        (lnssg10-is-sint32-p i3)
        (lnssg10-is-sint32-p x1)
        (lnssg10-is-sint32-p x)
        (lnssg10-valid-rw-p
         (lnssg10-shift a2 0)
         2147483646)
        (lnssg10-p-linked-n-p
         a a2 i2 x a1)
        (lnssg10-p-linked-n-p
         a a2 i2 i3 a3)
        (lnssg10-p-linked-n-p
         a3 a2 (+ i2 i3) (- (+ i i1) i3) a1))
       (lnssg10-p-linked-n-p
        a
        a2
        i2
        x1
        (lnssg10-t1
         (lnssg10-shift
          (lnssg10-t1
           (lnssg10-shift a2 (- (+ i2 i3) 2)))
          0))))))))

(value-triple :itpeval-statement-checked)

:q
