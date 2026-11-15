;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/contiki_memb/memb_alloc_Why3_ide_VCmemb_alloc_full_post_3_goal21:
;; the computed memb payload address is null under the stated full-bitmap,
;; scan, framing, memory-validity, and integer-range hypotheses. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun fp21-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun fp21-address-base (address)
  (car address))

(defun fp21-address-offset (address)
  (cdr address))

(defun fp21-shift (address amount)
  (cons
   (fp21-address-base address)
   (+ (fp21-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; pointer memory t_3, integer memories t_1 and t_2, allocation map t, region
;; function, and the linked and sconst predicates at the functions occurring
;; in this verification condition.

(defstub fp21-t3 (address) t)
(defstub fp21-t1 (address) t)
(defstub fp21-t2 (address) t)
(defstub fp21-allocation (index) t)
(defstub fp21-region (base) t)
(defstub fp21-linked-op () t)
(defstub fp21-sconst-op () t)

(defun-sk fp21-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (fp21-address-p address)
      (and
       (fp21-address-p (fp21-t3 address))
       (integerp (fp21-t1 address))
       (integerp (fp21-t2 address))))
     (implies
      (integerp index)
      (integerp (fp21-allocation index)))
     (implies
      (integerp base)
      (integerp (fp21-region base))))))

(defun fp21-linked-p ()
  (if (fp21-linked-op) t nil))

(defun fp21-sconst-p ()
  (if (fp21-sconst-op) t nil))

(defun fp21-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun fp21-is-uint16-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 65536)))

(defun fp21-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (fp21-address-base address))
    (<= 0 (fp21-address-offset address))
    (<=
     (+ (fp21-address-offset address) length)
     (fp21-allocation (fp21-address-base address))))))

(defun fp21-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (fp21-address-base address)))
    (<= 0 (fp21-address-offset address))
    (<=
     (+ (fp21-address-offset address) length)
     (fp21-allocation (fp21-address-base address))))))

(defun fp21-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (fp21-address-base left)
     (fp21-address-base right)))
   (<=
    (+ (fp21-address-offset right) right-length)
    (fp21-address-offset left))
   (<=
    (+ (fp21-address-offset left) left-length)
    (fp21-address-offset right))))

(defun-sk fp21-framed-p ()
  (forall (address)
    (implies
     (fp21-address-p address)
     (<=
      (fp21-region
       (fp21-address-base (fp21-t3 address)))
      0))))

;; Exact unfolding of Axiomatic13.p_valid_memb.

(defun fp21-p-valid-memb-p (m)
  (let*
      ((element-size
        (fp21-t1 (fp21-shift m 0)))
       (element-count
        (fp21-t1 (fp21-shift m 1)))
       (payload-size (* element-count element-size))
       (count-array
        (fp21-t3 (fp21-shift m 2)))
       (payload-array
        (fp21-t3 (fp21-shift m 3)))
       (count-start (fp21-shift count-array 0))
       (payload-start (fp21-shift payload-array 0)))
    (and
     (< 0 element-size)
     (<= payload-size 2147483647)
     (fp21-valid-rw-p m 4)
     (fp21-valid-rw-p count-array 1)
     (fp21-valid-rw-p payload-array 1)
     (fp21-valid-rw-p count-start element-count)
     (fp21-valid-rw-p payload-start payload-size)
     (fp21-separated-p
      count-start element-count payload-start payload-size))))

;; Exact unfolding of Axiomatic13.p__memb_full, retaining its universal
;; quantifier over every mathematical integer index.

(defun-sk fp21-p-memb-full-p (m)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index (fp21-t1 (fp21-shift m 1))))
     (not
      (equal
       (fp21-t2
        (fp21-shift
         (fp21-t3 (fp21-shift m 2))
         index))
       0)))))

;; The source scan hypothesis remains universally quantified over all integer
;; indices strictly before the current index.

(defun-sk fp21-earlier-slots-nonzero-p (array bound)
  (forall (index)
    (implies
     (and
      (integerp index)
      (<= 0 index)
      (< index bound))
     (not
      (equal
       (fp21-t2 (fp21-shift array index))
       0)))))

(defun-sk ntp4vc-memb-alloc-full-post-3-goal21-statement ()
  (forall
   (a i)
   (implies
    (and
     (fp21-function-types-p)
     (fp21-address-p a)
     (integerp i))
    (let*
        ((a1 (fp21-shift a 2))
         (a2 (fp21-t3 a1))
         (a3 (fp21-shift a2 i))
         (a4 (fp21-shift a 1))
         (x (fp21-t1 a4))
         (a5 (fp21-shift a 0))
         (x1 (fp21-t1 a5))
         (x2 (* i x1))
         (a6 (fp21-shift a 3)))
      (implies
       (and
        (equal (fp21-t2 a3) 0)
        (<= 0 i)
        (< i x)
        (<= (fp21-region (fp21-address-base a)) 0)
        (<= -2147483648 x2)
        (<= x2 2147483647)
        (fp21-framed-p)
        (fp21-linked-p)
        (fp21-sconst-p)
        (fp21-is-sint32-p i)
        (fp21-is-uint16-p x)
        (fp21-is-uint16-p x1)
        (fp21-p-valid-memb-p a)
        (fp21-p-memb-full-p a)
        (fp21-valid-rd-p a1 1)
        (fp21-valid-rd-p a6 1)
        (fp21-valid-rd-p a4 1)
        (fp21-valid-rd-p a5 1)
        (fp21-valid-rd-p a3 1)
        (fp21-valid-rw-p a3 1)
        (fp21-earlier-slots-nonzero-p a2 i))
       (equal
        (fp21-shift (fp21-t3 a6) x2)
        (cons 0 0)))))))

(value-triple :itpeval-statement-checked)

:q
