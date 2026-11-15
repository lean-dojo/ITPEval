;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_memb/memb_free_Why3_ide_VCmemb_free_loop_inv_established_goal3:
;; nonnegativity of the memb element count read at offset one under the stated
;; region, framing, memory-validity, and unsigned-integer hypotheses. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun mflieg3-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun mflieg3-address-base (address)
  (car address))

(defun mflieg3-address-offset (address)
  (cdr address))

(defun mflieg3-shift (address amount)
  (cons
   (mflieg3-address-base address)
   (+ (mflieg3-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; pointer memory t_3, integer memories t_1 and t_2, allocation map t, region
;; function, and the linked and sconst predicates at those functions.

(defstub mflieg3-t3 (address) t)
(defstub mflieg3-t1 (address) t)
(defstub mflieg3-allocation (index) t)
(defstub mflieg3-t2 (address) t)
(defstub mflieg3-region (base) t)
(defstub mflieg3-linked-op () t)
(defstub mflieg3-sconst-op () t)

(defun-sk mflieg3-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (mflieg3-address-p address)
      (and
       (mflieg3-address-p (mflieg3-t3 address))
       (integerp (mflieg3-t1 address))
       (integerp (mflieg3-t2 address))))
     (implies
      (integerp index)
      (integerp (mflieg3-allocation index)))
     (implies
      (integerp base)
      (integerp (mflieg3-region base))))))

(defun mflieg3-linked-p ()
  (if (mflieg3-linked-op) t nil))

(defun mflieg3-sconst-p ()
  (if (mflieg3-sconst-op) t nil))

(defun mflieg3-is-uint16-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 65536)))

(defun mflieg3-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (mflieg3-address-base address))
    (<= 0 (mflieg3-address-offset address))
    (<=
     (+ (mflieg3-address-offset address) length)
     (mflieg3-allocation (mflieg3-address-base address))))))

(defun mflieg3-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (mflieg3-address-base address)))
    (<= 0 (mflieg3-address-offset address))
    (<=
     (+ (mflieg3-address-offset address) length)
     (mflieg3-allocation (mflieg3-address-base address))))))

(defun mflieg3-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (mflieg3-address-base left)
     (mflieg3-address-base right)))
   (<=
    (+ (mflieg3-address-offset right) right-length)
    (mflieg3-address-offset left))
   (<=
    (+ (mflieg3-address-offset left) left-length)
    (mflieg3-address-offset right))))

(defun-sk mflieg3-framed-p ()
  (forall (address)
    (implies
     (mflieg3-address-p address)
     (<=
      (mflieg3-region
       (mflieg3-address-base (mflieg3-t3 address)))
      0))))

;; Exact unfolding of Axiomatic13.p_valid_memb.

(defun mflieg3-p-valid-memb-p (m)
  (let*
      ((element-size
        (mflieg3-t1 (mflieg3-shift m 0)))
       (element-count
        (mflieg3-t1 (mflieg3-shift m 1)))
       (payload-size (* element-count element-size))
       (count-array
        (mflieg3-t3 (mflieg3-shift m 2)))
       (payload-array
        (mflieg3-t3 (mflieg3-shift m 3)))
       (count-start (mflieg3-shift count-array 0))
       (payload-start (mflieg3-shift payload-array 0)))
    (and
     (< 0 element-size)
     (<= payload-size 2147483647)
     (mflieg3-valid-rw-p m 4)
     (mflieg3-valid-rw-p count-array 1)
     (mflieg3-valid-rw-p payload-array 1)
     (mflieg3-valid-rw-p count-start element-count)
     (mflieg3-valid-rw-p payload-start payload-size)
     (mflieg3-separated-p
      count-start element-count payload-start payload-size))))

(defun-sk
    ntp4vc-memb-free-loop-inv-established-goal3-statement ()
  (forall
   (a1 a)
   (implies
    (and
     (mflieg3-function-types-p)
     (mflieg3-address-p a1)
     (mflieg3-address-p a))
    (let ((x (mflieg3-t1 (mflieg3-shift a1 1))))
      (implies
       (and
        (<= (mflieg3-region (mflieg3-address-base a)) 0)
        (<= (mflieg3-region (mflieg3-address-base a1)) 0)
        (mflieg3-framed-p)
        (mflieg3-linked-p)
        (mflieg3-sconst-p)
        (mflieg3-is-uint16-p x)
        (mflieg3-p-valid-memb-p a1)
        (mflieg3-valid-rd-p (mflieg3-shift a1 3) 1))
       (<= 0 x))))))

(value-triple :itpeval-statement-checked)

:q
