;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/linked_n_split_segment_Why3_ide_VClinked_n_split_segment_loop_inv_4_established_goal13:
;; establishment of a zero-length suffix linked-list segment invariant while
;; splitting a list segment. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lnssg13-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lnssg13-address-base (address)
  (car address))

(defun lnssg13-address-offset (address)
  (cdr address))

(defun lnssg13-shift (address amount)
  (cons
   (lnssg13-address-base address)
   (+ (lnssg13-address-offset address) amount)))

;; These conservative symbols represent the universally arbitrary source
;; pointer function t_1, integer function t, region operation, and the linked
;; proposition specialized to t.

(defstub lnssg13-t1 (address) t)
(defstub lnssg13-t (index) t)
(defstub lnssg13-region (base) t)
(defstub lnssg13-linked-op () t)

(defun-sk lnssg13-function-types-p ()
  (forall (address index base)
    (implies
     (and
      (lnssg13-address-p address)
      (integerp index)
      (integerp base))
     (and
      (lnssg13-address-p (lnssg13-t1 address))
      (integerp (lnssg13-t index))
      (integerp (lnssg13-region base))))))

(defun lnssg13-linked-p ()
  (if (lnssg13-linked-op) t nil))

(defun lnssg13-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lnssg13-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lnssg13-address-base address))
    (<= 0 (lnssg13-address-offset address))
    (<=
     (+ (lnssg13-address-offset address) length)
     (lnssg13-t (lnssg13-address-base address))))))

;; This recursion is equivalent to the source inductive p_linked_n relation:
;; n = 0 is exactly its bound constructor, while n > 0 is exactly its cons
;; constructor followed by the unique recursive predecessor at n - 1.

(defun lnssg13-p-linked-n-p (root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (lnssg13-address-p root)
   (lnssg13-address-p array)
   (integerp index)
   (integerp n)
   (lnssg13-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (lnssg13-t1 (lnssg13-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (lnssg13-valid-rw-p root 4)
      (lnssg13-p-linked-n-p
       (lnssg13-t1 (lnssg13-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

(defun-sk lnssg13-framed-p ()
  (forall (address)
    (implies
     (lnssg13-address-p address)
     (<=
      (lnssg13-region
       (lnssg13-address-base (lnssg13-t1 address)))
      0))))

(defun-sk
    ntp4vc-linked-n-split-segment-loop-inv-4-established-goal13-statement ()
  (forall
   (i i1 i2 a a1 a2)
   (implies
    (and
     (lnssg13-function-types-p)
     (integerp i)
     (integerp i1)
     (integerp i2)
     (lnssg13-address-p a)
     (lnssg13-address-p a1)
     (lnssg13-address-p a2))
    (let ((x (+ i i1)))
      (implies
       (and
        (< 0 i)
        (<= 0 i1)
        (<= 0 i2)
        (<= (lnssg13-region (lnssg13-address-base a)) 0)
        (<= (lnssg13-region (lnssg13-address-base a1)) 0)
        (<= (lnssg13-region (lnssg13-address-base a2)) 0)
        (<=
         (lnssg13-region
          (lnssg13-address-base
           (lnssg13-t1
            (lnssg13-shift
             (lnssg13-t1
              (lnssg13-shift a2 (- (+ i i2) 1)))
             0))))
         0)
        (lnssg13-framed-p)
        (lnssg13-linked-p)
        (lnssg13-is-sint32-p i)
        (lnssg13-is-sint32-p i1)
        (lnssg13-is-sint32-p i2)
        (lnssg13-is-sint32-p x)
        (lnssg13-valid-rw-p
         (lnssg13-shift a2 0)
         2147483646)
        (lnssg13-p-linked-n-p
         a a2 i2 x a1))
       (lnssg13-p-linked-n-p
        (lnssg13-t1
         (lnssg13-shift
          (lnssg13-t1
           (lnssg13-shift a2 (- (+ i i1 i2) 1)))
          0))
        a2
        (+ i i1 i2)
        0
        a1))))))

(value-triple :itpeval-statement-checked)

:q
