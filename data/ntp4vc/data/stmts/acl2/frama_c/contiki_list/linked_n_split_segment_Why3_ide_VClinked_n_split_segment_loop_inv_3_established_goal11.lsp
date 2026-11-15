;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_list/linked_n_split_segment_Why3_ide_VClinked_n_split_segment_loop_inv_3_established_goal11:
;; establishment of the endpoint of an inductively defined linked-list segment
;; during segment splitting. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun lnssg11-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun lnssg11-address-base (address)
  (car address))

(defun lnssg11-address-offset (address)
  (cdr address))

(defun lnssg11-shift (address amount)
  (cons
   (lnssg11-address-base address)
   (+ (lnssg11-address-offset address) amount)))

;; These conservative symbols represent the universally arbitrary source
;; pointer function t_1, integer function t, region operation, and the linked
;; proposition specialized to t.

(defstub lnssg11-t1 (address) t)
(defstub lnssg11-t (index) t)
(defstub lnssg11-region (base) t)
(defstub lnssg11-linked-op () t)

(defun-sk lnssg11-function-types-p ()
  (forall (address index base)
    (implies
     (and
      (lnssg11-address-p address)
      (integerp index)
      (integerp base))
     (and
      (lnssg11-address-p (lnssg11-t1 address))
      (integerp (lnssg11-t index))
      (integerp (lnssg11-region base))))))

(defun lnssg11-linked-p ()
  (if (lnssg11-linked-op) t nil))

(defun lnssg11-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun lnssg11-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (lnssg11-address-base address))
    (<= 0 (lnssg11-address-offset address))
    (<=
     (+ (lnssg11-address-offset address) length)
     (lnssg11-t (lnssg11-address-base address))))))

;; This recursion is equivalent to the source inductive p_linked_n relation:
;; n = 0 is exactly its bound constructor, while n > 0 is exactly its cons
;; constructor followed by the unique recursive predecessor at n - 1.

(defun lnssg11-p-linked-n-p (root array index n bound)
  (declare (xargs :measure (nfix n)))
  (and
   (lnssg11-address-p root)
   (lnssg11-address-p array)
   (integerp index)
   (integerp n)
   (lnssg11-address-p bound)
   (if (equal n 0)
       (and
        (equal root bound)
        (<= 0 index)
        (<= index 2147483646))
     (and
      (< 0 n)
      (equal
       (lnssg11-t1 (lnssg11-shift array index))
       root)
      (<= 0 index)
      (<= 0 (+ index n))
      (<= (+ index n) 2147483646)
      (lnssg11-valid-rw-p root 4)
      (lnssg11-p-linked-n-p
       (lnssg11-t1 (lnssg11-shift root 0))
       array
       (+ 1 index)
       (- n 1)
       bound)))))

(defun-sk lnssg11-framed-p ()
  (forall (address)
    (implies
     (lnssg11-address-p address)
     (<=
      (lnssg11-region
       (lnssg11-address-base (lnssg11-t1 address)))
      0))))

(defun-sk
    ntp4vc-linked-n-split-segment-loop-inv-3-established-goal11-statement ()
  (forall
   (i i1 i2 a a1 a2)
   (implies
    (and
     (lnssg11-function-types-p)
     (integerp i)
     (integerp i1)
     (integerp i2)
     (lnssg11-address-p a)
     (lnssg11-address-p a1)
     (lnssg11-address-p a2))
    (let ((x (+ i i1)))
      (implies
       (and
        (< 0 i)
        (<= 0 i1)
        (<= 0 i2)
        (<= (lnssg11-region (lnssg11-address-base a)) 0)
        (<= (lnssg11-region (lnssg11-address-base a1)) 0)
        (<= (lnssg11-region (lnssg11-address-base a2)) 0)
        (<=
         (lnssg11-region
          (lnssg11-address-base
           (lnssg11-t1
            (lnssg11-shift
             (lnssg11-t1
              (lnssg11-shift a2 (- (+ i i2) 1)))
             0))))
         0)
        (lnssg11-framed-p)
        (lnssg11-linked-p)
        (lnssg11-is-sint32-p i)
        (lnssg11-is-sint32-p i1)
        (lnssg11-is-sint32-p i2)
        (lnssg11-is-sint32-p x)
        (lnssg11-valid-rw-p
         (lnssg11-shift a2 0)
         2147483646)
        (lnssg11-p-linked-n-p
         a a2 i2 x a1))
       (lnssg11-p-linked-n-p
        a
        a2
        i2
        x
        (lnssg11-t1
         (lnssg11-shift
          (lnssg11-t1
           (lnssg11-shift a2 (- (+ i i1 i2) 1)))
          0))))))))

(value-triple :itpeval-statement-checked)

:q
