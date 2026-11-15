;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/x509_parser/parse_UTCTime_Why3_ide_VCparse_UTCTime_call_compute_decimal_pre_part1_3_goal17:
;; the decimal-digit lower bound for the byte at parser offset six under the
;; stated address, integer-range, memory-validity, separation, and digit-prefix
;; hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun utc17-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun utc17-address-base (address)
  (car address))

(defun utc17-address-offset (address)
  (cdr address))

(defun utc17-shift (address amount)
  (cons
   (utc17-address-base address)
   (+ (utc17-address-offset address) amount)))

;; These conservative interfaces represent the universally arbitrary source
;; byte memory t_1 and allocation map t, together with the fixed source region
;; function and the linked proposition specialized to t.

(defstub utc17-byte-memory (address) t)
(defstub utc17-allocation (index) t)
(defstub utc17-region (base) t)
(defstub utc17-linked-op () t)

(defun-sk utc17-function-types-p ()
  (forall (address index base)
    (and
     (implies
      (utc17-address-p address)
      (integerp (utc17-byte-memory address)))
     (implies
      (integerp index)
      (integerp (utc17-allocation index)))
     (implies
      (integerp base)
      (integerp (utc17-region base))))))

(defun utc17-linked-p ()
  (if (utc17-linked-op) t nil))

(defun utc17-is-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

(defun utc17-is-uint16-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 65536)))

;; Exact unfoldings of Memory.valid_rw, Memory.valid_rd, and Memory.separated.

(defun utc17-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0 (utc17-address-base address))
    (<= 0 (utc17-address-offset address))
    (<=
     (+ (utc17-address-offset address) length)
     (utc17-allocation (utc17-address-base address))))))

(defun utc17-valid-rd-p (address length)
  (implies
   (< 0 length)
   (and
    (not (equal 0 (utc17-address-base address)))
    (<= 0 (utc17-address-offset address))
    (<=
     (+ (utc17-address-offset address) length)
     (utc17-allocation (utc17-address-base address))))))

(defun utc17-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (utc17-address-base left)
     (utc17-address-base right)))
   (<=
    (+ (utc17-address-offset right) right-length)
    (utc17-address-offset left))
   (<=
    (+ (utc17-address-offset left) left-length)
    (utc17-address-offset right))))

;; Preserve the source universal condition over every mathematical integer
;; index i_4 from zero (inclusive) to i_2 (exclusive).

(defun-sk utc17-decimal-prefix-p (a7 i2)
  (forall (i4)
    (implies
     (integerp i4)
     (let
         ((x5
           (utc17-byte-memory
            (utc17-shift a7 (+ 2 i4)))))
       (implies
        (<= 0 i4)
        (implies
         (< i4 i2)
         (and
          (<= 48 x5)
          (<= x5 57))))))))

(defun-sk
    ntp4vc-parse-utctime-call-compute-decimal-pre-part1-3-goal17-statement ()
  (forall
   (a7 a1 a a2 a3 a4 a5 a6 i i1 i3 i2)
   (implies
    (and
     (utc17-function-types-p)
     (utc17-address-p a7)
     (utc17-address-p a1)
     (utc17-address-p a)
     (utc17-address-p a2)
     (utc17-address-p a3)
     (utc17-address-p a4)
     (utc17-address-p a5)
     (utc17-address-p a6)
     (integerp i)
     (integerp i1)
     (integerp i3)
     (integerp i2))
    (let*
        ((a8 (utc17-shift a7 0))
         (a9 (utc17-shift a7 1))
         (a10 (utc17-shift a7 14))
         (a11 (utc17-shift a7 2))
         (x (utc17-byte-memory a11))
         (a12 (utc17-shift a7 3))
         (x1 (utc17-byte-memory a12))
         (a13 (utc17-shift a7 4))
         (x2 (utc17-byte-memory a13))
         (a14 (utc17-shift a7 5))
         (x3 (utc17-byte-memory a14))
         (a15 (utc17-shift a7 6))
         (x4 (utc17-byte-memory a15))
         (a16 (utc17-shift a7 7)))
      (implies
       (and
        (not (equal a1 a))
        (not (equal a2 a))
        (not (equal a2 a1))
        (not (equal a3 a))
        (not (equal a3 a1))
        (not (equal a3 a2))
        (not (equal a4 a))
        (not (equal a4 a1))
        (not (equal a4 a2))
        (not (equal a4 a3))
        (not (equal a5 a))
        (not (equal a5 a1))
        (not (equal a5 a2))
        (not (equal a5 a3))
        (not (equal a5 a4))
        (not (equal a6 a))
        (not (equal a6 a1))
        (not (equal a6 a2))
        (not (equal a6 a3))
        (not (equal a6 a4))
        (not (equal a6 a5))
        (not (equal (cons 0 0) a7))
        (equal (utc17-byte-memory a8) 23)
        (equal (utc17-byte-memory a9) 13)
        (equal (utc17-byte-memory a10) 90)
        (<= 0 i)
        (<= 0 i1)
        (<= 0 i3)
        (<= (utc17-region (utc17-address-base a)) 0)
        (<= (utc17-region (utc17-address-base a1)) 0)
        (<= (utc17-region (utc17-address-base a2)) 0)
        (<= (utc17-region (utc17-address-base a3)) 0)
        (<= (utc17-region (utc17-address-base a4)) 0)
        (<= (utc17-region (utc17-address-base a5)) 0)
        (<= (utc17-region (utc17-address-base a6)) 0)
        (<= (utc17-region (utc17-address-base a7)) 0)
        (<= -1900 i)
        (<= 12 i2)
        (<= 15 i1)
        (<= 50 i)
        (<= i 99)
        (<= i3 99)
        (<= i 63635)
        (<= i 2147481747)
        (<= 48 x)
        (<= 48 x1)
        (<= 48 x2)
        (<= 48 x3)
        (<= x 57)
        (<= x1 57)
        (<= x2 57)
        (<= x3 57)
        (utc17-linked-p)
        (utc17-is-uint8-p i)
        (utc17-is-uint8-p i2)
        (utc17-is-uint8-p i3)
        (utc17-is-uint16-p i)
        (utc17-is-uint16-p i1)
        (utc17-valid-rw-p a 1)
        (utc17-valid-rw-p a1 1)
        (utc17-valid-rw-p a2 1)
        (utc17-valid-rw-p a3 1)
        (utc17-valid-rw-p a4 1)
        (utc17-valid-rw-p a5 1)
        (utc17-valid-rw-p a6 1)
        (utc17-is-uint8-p x)
        (utc17-is-uint8-p x1)
        (utc17-is-uint8-p x2)
        (utc17-is-uint8-p x3)
        (utc17-is-uint8-p x4)
        (utc17-is-uint8-p (utc17-byte-memory a16))
        (utc17-valid-rd-p a8 1)
        (utc17-valid-rd-p a9 1)
        (utc17-valid-rd-p a11 1)
        (utc17-valid-rd-p a12 1)
        (utc17-valid-rd-p a13 1)
        (utc17-valid-rd-p a14 1)
        (utc17-valid-rd-p a15 1)
        (utc17-valid-rd-p a16 1)
        (utc17-valid-rd-p a10 1)
        (utc17-separated-p a 1 a8 i1)
        (utc17-separated-p a1 1 a8 i1)
        (utc17-separated-p a2 1 a8 i1)
        (utc17-separated-p a3 1 a8 i1)
        (utc17-separated-p a4 1 a8 i1)
        (utc17-separated-p a5 1 a8 i1)
        (utc17-separated-p a6 1 a8 i1)
        (utc17-valid-rd-p
         (utc17-shift a7 (+ 2 i2))
         1)
        (implies
         (< 0 i1)
         (utc17-valid-rd-p a8 i1))
        (utc17-decimal-prefix-p a7 i2))
       (<= 48 x4))))))

(value-triple :itpeval-statement-checked)

:q
