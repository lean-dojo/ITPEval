;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/sysfs_streq_Why3_ide_VCsysfs_streq_assert_8_goal16:
;; the sysfs string-equality verification condition concluding that the
;; newline-terminated first string has logical sysfs length equal to the
;; shared prefix index, under the stated memory, string-validity, comparison,
;; region, linkedness, constancy, and quantified prefix hypotheses.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun ss8g16-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun ss8g16-address-base (address)
  (car address))

(defun ss8g16-address-offset (address)
  (cdr address))

(defun ss8g16-shift (address amount)
  (cons
   (ss8g16-address-base address)
   (+ (ss8g16-address-offset address)
      amount)))

;; Conservative interfaces represent the universally arbitrary character
;; memory t_1 and allocation map t, together with the source region, logical
;; strlen, logical sysfs strlen, logical strncmp, C integer conversions,
;; linkedness, and constancy symbols.

(defstub ss8g16-character-memory (address) t)
(defstub ss8g16-allocation (index) t)
(defstub ss8g16-region (base) t)
(defstub ss8g16-l-strlen (address) t)
(defstub ss8g16-l-sysfs-strlen (address) t)
(defstub ss8g16-l-strncmp (left right count) t)
(defstub ss8g16-to-uint64 (value) t)
(defstub ss8g16-to-sint32 (value) t)
(defstub ss8g16-linked-op () t)
(defstub ss8g16-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk ss8g16-function-types-p ()
  (forall (address index base value left right count)
    (and
     (implies
      (ss8g16-address-p address)
      (and
       (integerp
        (ss8g16-character-memory address))
       (integerp
        (ss8g16-l-strlen address))
       (integerp
        (ss8g16-l-sysfs-strlen address))))
     (implies
      (integerp index)
      (integerp
       (ss8g16-allocation index)))
     (implies
      (integerp base)
      (integerp
       (ss8g16-region base)))
     (implies
      (integerp value)
      (and
       (integerp
        (ss8g16-to-uint64 value))
       (integerp
        (ss8g16-to-sint32 value))))
     (implies
      (and
       (ss8g16-address-p left)
       (ss8g16-address-p right)
       (integerp count))
      (integerp
       (ss8g16-l-strncmp left right count))))))

(defun ss8g16-linked-p ()
  (if (ss8g16-linked-op) t nil))

(defun ss8g16-sconst-p ()
  (if (ss8g16-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun ss8g16-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun ss8g16-is-sint32-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (< value 2147483648)))

(defun ss8g16-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source C
;; integer conversions used by the three logical string recurrences.

(defun-sk ss8g16-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (ss8g16-is-uint64-p
       (ss8g16-to-uint64 value))
      (implies
       (ss8g16-is-uint64-p value)
       (equal
        (ss8g16-to-uint64 value)
        value))
      (equal
       (ss8g16-to-uint64
        (ss8g16-to-uint64 value))
       (ss8g16-to-uint64 value))))))

(defun-sk ss8g16-to-sint32-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (ss8g16-is-sint32-p
       (ss8g16-to-sint32 value))
      (implies
       (ss8g16-is-sint32-p value)
       (equal
        (ss8g16-to-sint32 value)
        value))
      (equal
       (ss8g16-to-sint32
        (ss8g16-to-sint32 value))
       (ss8g16-to-sint32 value))))))

;; Exact unfolding of Memory.valid_rw for the arbitrary allocation map t.

(defun ss8g16-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (ss8g16-address-base address))
    (<= 0
        (ss8g16-address-offset address))
    (<=
     (+ (ss8g16-address-offset address)
        length)
     (ss8g16-allocation
      (ss8g16-address-base address))))))

;; Exact unfolding of A_Strlen.p_valid_str. Its null terminator remains an
;; internal existential over all mathematical integers, and its character
;; range condition remains universally quantified over all integers.

(defun-sk ss8g16-string-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (ss8g16-is-sint8-p
       (ss8g16-character-memory
        (ss8g16-shift address position)))))))

(defun-sk ss8g16-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (ss8g16-character-memory
       (ss8g16-shift address index))
      0)
     (ss8g16-is-uint64-p index)
     (ss8g16-valid-rw-p
      (ss8g16-shift address 0)
      (+ 1 index))
     (ss8g16-string-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen.

(defun-sk ss8g16-strlen-laws-p ()
  (forall (address)
    (implies
     (ss8g16-address-p address)
     (and
      (if
          (equal
           (ss8g16-character-memory
            (ss8g16-shift address 0))
           0)
          (equal
           (ss8g16-l-strlen address)
           0)
        (equal
         (ss8g16-to-uint64
          (+ 1
             (ss8g16-l-strlen
              (ss8g16-shift address 1))))
         (ss8g16-l-strlen address)))
      (ss8g16-is-uint64-p
       (ss8g16-l-strlen address))))))

;; Universal closures of A_SysfsStr.fix_l_sysfs_strlen and
;; Q_TL_sysfs_strlen.

(defun-sk ss8g16-sysfs-strlen-laws-p ()
  (forall (address)
    (implies
     (ss8g16-address-p address)
     (and
      (if
          (or
           (equal
            (ss8g16-character-memory
             (ss8g16-shift address 0))
            0)
           (and
            (equal
             (ss8g16-character-memory
              (ss8g16-shift address 0))
             10)
            (equal
             (ss8g16-character-memory
              (ss8g16-shift address 1))
             0)))
          (equal
           (ss8g16-l-sysfs-strlen address)
           0)
        (equal
         (ss8g16-to-uint64
          (+ 1
             (ss8g16-l-sysfs-strlen
              (ss8g16-shift address 1))))
         (ss8g16-l-sysfs-strlen address)))
      (ss8g16-is-uint64-p
       (ss8g16-l-sysfs-strlen address))))))

;; Universal closures of A_StrnCmp.fix_l_strncmp_2' and Q_TL_strncmp_2'.

(defun-sk ss8g16-strncmp-laws-p ()
  (forall (left right count)
    (implies
     (and
      (ss8g16-address-p left)
      (ss8g16-address-p right)
      (integerp count))
     (and
      (if
          (equal count 0)
          (equal
           (ss8g16-l-strncmp left right count)
           0)
        (if
            (equal
             (ss8g16-character-memory
              (ss8g16-shift right 0))
             (ss8g16-character-memory
              (ss8g16-shift left 0)))
            (if
                (equal
                 (ss8g16-character-memory
                  (ss8g16-shift left 0))
                 0)
                (equal
                 (ss8g16-l-strncmp left right count)
                 0)
              (equal
               (ss8g16-l-strncmp
                (ss8g16-shift left 1)
                (ss8g16-shift right 1)
                (ss8g16-to-uint64 (- count 1)))
               (ss8g16-l-strncmp left right count)))
          (equal
           (ss8g16-to-sint32
            (-
             (ss8g16-character-memory
              (ss8g16-shift left 0))
             (ss8g16-character-memory
              (ss8g16-shift right 0))))
           (ss8g16-l-strncmp left right count))))
      (ss8g16-is-sint32-p
       (ss8g16-l-strncmp left right count))))))

(defun ss8g16-strnequal-p (left right count)
  (equal
   (ss8g16-l-strncmp left right count)
   0))

;; The two source prefix hypotheses retain their universal quantifiers over
;; every mathematical integer and their original strict upper bound.

(defun-sk ss8g16-prefix-equal-before-p
    (left right bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= 0 position)
      (implies
       (< position bound)
       (equal
        (ss8g16-character-memory
         (ss8g16-shift left position))
        (ss8g16-character-memory
         (ss8g16-shift right position))))))))

(defun-sk ss8g16-prefix-nonzero-and-equal-before-p
    (left right bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= 0 position)
      (implies
       (< position bound)
       (and
        (not
         (equal
          (ss8g16-character-memory
           (ss8g16-shift right position))
          0))
        (not
         (equal
          (ss8g16-character-memory
           (ss8g16-shift left position))
          0))
        (equal
         (ss8g16-character-memory
          (ss8g16-shift left position))
         (ss8g16-character-memory
          (ss8g16-shift right position)))))))))

(defun-sk
    ntp4vc-sysfs-streq-assert-8-goal16-statement ()
  (forall
   (a i a1)
   (implies
    (and
     (ss8g16-address-p a)
     (integerp i)
     (ss8g16-address-p a1)
     (ss8g16-function-types-p)
     (ss8g16-to-uint64-laws-p)
     (ss8g16-to-sint32-laws-p)
     (ss8g16-strlen-laws-p)
     (ss8g16-sysfs-strlen-laws-p)
     (ss8g16-strncmp-laws-p))
    (let*
        ((a2
          (ss8g16-shift a i))
         (a3
          (ss8g16-shift a1 i))
         (x
          (ss8g16-l-sysfs-strlen a2)))
      (implies
       (and
        (equal
         (ss8g16-character-memory a2)
         10)
        (equal
         (ss8g16-character-memory a3)
         0)
        (equal
         (ss8g16-l-sysfs-strlen a3)
         x)
        (equal
         (ss8g16-character-memory
          (ss8g16-shift a (+ 1 i)))
         0)
        (<= i
            (ss8g16-l-strlen a))
        (<= i
            (ss8g16-l-strlen a1))
        (<=
         (ss8g16-region
          (ss8g16-address-base a))
         0)
        (<=
         (ss8g16-region
          (ss8g16-address-base a1))
         0)
        (ss8g16-linked-p)
        (ss8g16-sconst-p)
        (ss8g16-is-uint64-p i)
        (ss8g16-valid-string-p a)
        (ss8g16-valid-string-p a1)
        (ss8g16-strnequal-p a1 a i)
        (ss8g16-valid-string-p a2)
        (ss8g16-valid-string-p a3)
        (ss8g16-strnequal-p a3 a2 x)
        (ss8g16-prefix-equal-before-p
         a1 a i)
        (ss8g16-prefix-nonzero-and-equal-before-p
         a1 a i))
       (equal
        (ss8g16-l-sysfs-strlen a)
        i))))))

(value-triple :itpeval-statement-checked)

:q
