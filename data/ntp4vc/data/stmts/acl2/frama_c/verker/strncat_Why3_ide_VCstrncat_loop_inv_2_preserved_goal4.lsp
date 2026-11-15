;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strncat_Why3_ide_VCstrncat_loop_inv_2_preserved_goal4:
;; preservation of valid-string memory after advancing the current strncat
;; destination pointer, under the stated bounded-source, memory-validity,
;; address-order, character-range, and non-null-prefix hypotheses. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun snc4-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun snc4-address-base (address)
  (car address))

(defun snc4-address-offset (address)
  (cdr address))

(defun snc4-shift (address amount)
  (cons
   (snc4-address-base address)
   (+ (snc4-address-offset address) amount)))

;; Conservative interfaces represent the arbitrary source functions.

(defstub snc4-character-memory (address) t)
(defstub snc4-allocation (index) t)
(defstub snc4-region (base) t)
(defstub snc4-addr-le-op (left right) t)
(defstub snc4-l-strlen (address) t)
(defstub snc4-l-strnlen (address count) t)
(defstub snc4-to-uint64 (value) t)
(defstub snc4-linked-op () t)
(defstub snc4-sconst-op () t)

;; Preserve all source function types over addresses and unbounded integers.

(defun-sk snc4-function-types-p ()
  (forall (address index base count value)
    (and
     (implies
      (snc4-address-p address)
      (and
       (integerp
        (snc4-character-memory address))
       (integerp
        (snc4-l-strlen address))))
     (implies
      (and
       (snc4-address-p address)
       (integerp count))
      (integerp
       (snc4-l-strnlen address count)))
     (implies
      (integerp index)
      (integerp
       (snc4-allocation index)))
     (implies
      (integerp base)
      (integerp
       (snc4-region base)))
     (implies
      (integerp value)
      (integerp
       (snc4-to-uint64 value))))))

(defun snc4-addr-le-p (left right)
  (if (snc4-addr-le-op left right) t nil))

;; On equal-base addresses, addr_le is exactly integer order on offsets.

(defun-sk snc4-address-order-law-p ()
  (forall (left right)
    (implies
     (and
      (snc4-address-p left)
      (snc4-address-p right)
      (equal
       (snc4-address-base left)
       (snc4-address-base right)))
     (equal
      (snc4-addr-le-p left right)
      (<=
       (snc4-address-offset left)
       (snc4-address-offset right))))))

(defun snc4-linked-p ()
  (if (snc4-linked-op) t nil))

(defun snc4-sconst-p ()
  (if (snc4-sconst-op) t nil))

(defun snc4-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun snc4-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Exact range, identity, and projection laws for Cint.to_uint64.

(defun-sk snc4-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (snc4-is-uint64-p
       (snc4-to-uint64 value))
      (implies
       (snc4-is-uint64-p value)
       (equal
        (snc4-to-uint64 value)
        value))
      (equal
       (snc4-to-uint64
        (snc4-to-uint64 value))
       (snc4-to-uint64 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map.

(defun snc4-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (snc4-address-base address))
    (<= 0
        (snc4-address-offset address))
    (<=
     (+ (snc4-address-offset address)
        length)
     (snc4-allocation
      (snc4-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str.

(defun-sk snc4-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (snc4-is-sint8-p
       (snc4-character-memory
        (snc4-shift address position)))))))

(defun-sk snc4-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (snc4-character-memory
       (snc4-shift address index))
      0)
     (snc4-is-uint64-p index)
     (snc4-valid-rw-p
      (snc4-shift address 0)
      (+ 1 index))
     (snc4-string-chars-sint8-through-p
      address index))))

;; Exact unfolding of A_Strnlen.p_valid_strn. Its terminating position stays
;; existentially quantified, and its character condition stays universal.

(defun-sk snc4-bounded-string-terminator-p
    (address count)
  (exists (index)
    (and
     (integerp index)
     (equal
      (snc4-character-memory
       (snc4-shift address index))
      0)
     (< index count)
     (snc4-is-uint64-p index)
     (snc4-valid-rw-p
      (snc4-shift address 0)
      (+ 1 index)))))

(defun-sk snc4-bounded-string-chars-p
    (address count)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position count)
      (snc4-is-sint8-p
       (snc4-character-memory
        (snc4-shift address position)))))))

(defun snc4-valid-stringn-p (address count)
  (or
   (snc4-valid-rw-p
    (snc4-shift address 0)
    (+ 1 count))
   (and
    (snc4-bounded-string-terminator-p
     address count)
    (snc4-bounded-string-chars-p
     address count))))

;; Universal closures of the logical strlen specification.

(defun-sk snc4-strlen-laws-p ()
  (forall (address)
    (implies
     (snc4-address-p address)
     (and
      (if
          (equal
           (snc4-character-memory
            (snc4-shift address 0))
           0)
          (equal
           (snc4-l-strlen address)
           0)
        (equal
         (snc4-to-uint64
          (+ 1
             (snc4-l-strlen
              (snc4-shift address 1))))
         (snc4-l-strlen address)))
      (snc4-is-uint64-p
       (snc4-l-strlen address))))))

;; Universal closures of the logical strnlen specification.

(defun-sk snc4-strnlen-laws-p ()
  (forall (address count)
    (implies
     (and
      (snc4-address-p address)
      (integerp count))
     (and
      (if
          (or
           (equal count 0)
           (equal
            (snc4-character-memory
             (snc4-shift address 0))
            0))
          (equal
           (snc4-l-strnlen address count)
           0)
        (equal
         (snc4-to-uint64
          (+ 1
             (snc4-l-strnlen
              (snc4-shift address 1)
              (snc4-to-uint64
               (- count 1)))))
         (snc4-l-strnlen address count)))
      (snc4-is-uint64-p
       (snc4-l-strnlen address count))))))

;; The loop hypotheses retain their internal integer quantifiers.

(defun-sk snc4-no-null-through-count-p
    (address count)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= 0 position)
      (implies
       (<= position count)
       (not
        (equal
         (snc4-character-memory
          (snc4-shift address position))
         0)))))))

(defun-sk snc4-null-at-or-before-count-p
    (address count)
  (exists (position)
    (and
     (integerp position)
     (equal
      (snc4-character-memory
       (snc4-shift address position))
      0)
     (<= 0 position)
     (<= position count))))

(defun-sk snc4-no-null-before-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= 0 position)
      (implies
       (< position bound)
       (not
        (equal
         (snc4-character-memory
          (snc4-shift address position))
         0)))))))

(defun-sk
    ntp4vc-strncat-loop-inv-2-preserved-goal4-statement ()
  (forall
   (a2 a a1 i)
   (implies
    (and
     (snc4-address-p a2)
     (snc4-address-p a)
     (snc4-address-p a1)
     (integerp i)
     (snc4-function-types-p)
     (snc4-address-order-law-p)
     (snc4-to-uint64-laws-p)
     (snc4-strlen-laws-p)
     (snc4-strnlen-laws-p))
    (let*
        ((x
          (snc4-character-memory a2))
         (x1
          (snc4-l-strlen a))
         (a3
          (snc4-shift a x1))
         (x2
          (snc4-l-strnlen a1 i))
         (x3
          (snc4-character-memory
           (snc4-shift a1 x2))))
      (implies
       (and
        (not (equal i 0))
        (not (equal x 0))
        (equal
         (snc4-character-memory a3)
         0)
        (<=
         (snc4-region
          (snc4-address-base a))
         0)
        (<=
         (snc4-region
          (snc4-address-base a1))
         0)
        (<=
         (+ i x1)
         18446744073709551615)
        (snc4-linked-p)
        (snc4-sconst-p)
        (snc4-is-uint64-p i)
        (snc4-addr-le-p a a2)
        (snc4-is-sint8-p x)
        (snc4-valid-string-p a)
        (snc4-valid-string-p a2)
        (snc4-is-uint64-p x1)
        (snc4-valid-stringn-p a1 i)
        (snc4-is-uint64-p x2)
        (snc4-addr-le-p a2 a3)
        (snc4-is-sint8-p x3)
        (snc4-valid-rw-p
         (snc4-shift a 0)
         (+ 1 i x1))
        (implies
         (snc4-no-null-through-count-p
          a1 i)
         (equal x2 i))
        (implies
         (snc4-null-at-or-before-count-p
          a1 i)
         (equal x3 0))
        (implies
         (snc4-null-at-or-before-count-p
          a1 i)
         (snc4-no-null-before-p
          a1 x2))
        (snc4-no-null-before-p
         a x1))
       (snc4-valid-string-p
        (snc4-shift a2 1)))))))

(value-triple :itpeval-statement-checked)

:q
