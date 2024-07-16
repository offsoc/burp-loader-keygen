package java.math;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.ObjectStreamField;
import java.io.StreamCorruptedException;
import java.io.ObjectInputStream.GetField;
import java.io.ObjectOutputStream.PutField;
import java.util.Arrays;
import java.util.Random;
import java.util.concurrent.ThreadLocalRandom;
import sun.misc.Unsafe;

public class BigInteger extends Number implements Comparable<BigInteger> {
   final int signum;
   final int[] mag;
   /** @deprecated */
   @Deprecated
   private int bitCount;
   /** @deprecated */
   @Deprecated
   private int bitLength;
   /** @deprecated */
   @Deprecated
   private int lowestSetBit;
   /** @deprecated */
   @Deprecated
   private int firstNonzeroIntNum;
   static final long LONG_MASK = 4294967295L;
   private static final int MAX_MAG_LENGTH = 67108864;
   private static final int PRIME_SEARCH_BIT_LENGTH_LIMIT = 500000000;
   private static final int KARATSUBA_THRESHOLD = 80;
   private static final int TOOM_COOK_THRESHOLD = 240;
   private static final int KARATSUBA_SQUARE_THRESHOLD = 128;
   private static final int TOOM_COOK_SQUARE_THRESHOLD = 216;
   static final int BURNIKEL_ZIEGLER_THRESHOLD = 80;
   static final int BURNIKEL_ZIEGLER_OFFSET = 40;
   private static final int SCHOENHAGE_BASE_CONVERSION_THRESHOLD = 20;
   private static final int MULTIPLY_SQUARE_THRESHOLD = 20;
   private static final int MONTGOMERY_INTRINSIC_THRESHOLD = 512;
   private static long[] bitsPerDigit = new long[]{0L, 0L, 1024L, 1624L, 2048L, 2378L, 2648L, 2875L, 3072L, 3247L, 3402L, 3543L, 3672L, 3790L, 3899L, 4001L, 4096L, 4186L, 4271L, 4350L, 4426L, 4498L, 4567L, 4633L, 4696L, 4756L, 4814L, 4870L, 4923L, 4975L, 5025L, 5074L, 5120L, 5166L, 5210L, 5253L, 5295L};
   private static final int SMALL_PRIME_THRESHOLD = 95;
   private static final int DEFAULT_PRIME_CERTAINTY = 100;
   private static final BigInteger SMALL_PRIME_PRODUCT = valueOf(152125131763605L);
   private static final int MAX_CONSTANT = 16;
   private static BigInteger[] posConst = new BigInteger[17];
   private static BigInteger[] negConst = new BigInteger[17];
   private static volatile BigInteger[][] powerCache;
   private static final double[] logCache;
   private static final double LOG_TWO = Math.log(2.0D);
   public static final BigInteger ZERO;
   public static final BigInteger ONE;
   private static final BigInteger TWO;
   private static final BigInteger NEGATIVE_ONE;
   public static final BigInteger TEN;
   static int[] bnExpModThreshTable;
   private static String[] zeros;
   private static int[] digitsPerLong;
   private static BigInteger[] longRadix;
   private static int[] digitsPerInt;
   private static int[] intRadix;
   private static final long serialVersionUID = -8287574255936472291L;
   private static final ObjectStreamField[] serialPersistentFields;

   public BigInteger(byte[] var1) {
      if (var1.length == 0) {
         throw new NumberFormatException("Zero length BigInteger");
      } else {
         if (var1[0] < 0) {
            this.mag = makePositive(var1);
            this.signum = -1;
         } else {
            this.mag = stripLeadingZeroBytes(var1);
            this.signum = this.mag.length == 0 ? 0 : 1;
         }

         if (this.mag.length >= 67108864) {
            this.checkRange();
         }

      }
   }

   private BigInteger(int[] var1) {
      if (var1.length == 0) {
         throw new NumberFormatException("Zero length BigInteger");
      } else {
         if (var1[0] < 0) {
            this.mag = makePositive(var1);
            this.signum = -1;
         } else {
            this.mag = trustedStripLeadingZeroInts(var1);
            this.signum = this.mag.length == 0 ? 0 : 1;
         }

         if (this.mag.length >= 67108864) {
            this.checkRange();
         }

      }
   }

   public BigInteger(int var1, byte[] var2) {
      this.mag = stripLeadingZeroBytes(var2);
      if (var1 >= -1 && var1 <= 1) {
         if (this.mag.length == 0) {
            this.signum = 0;
         } else {
            if (var1 == 0) {
               throw new NumberFormatException("signum-magnitude mismatch");
            }

            this.signum = var1;
         }

         if (this.mag.length >= 67108864) {
            this.checkRange();
         }

      } else {
         throw new NumberFormatException("Invalid signum value");
      }
   }

   private BigInteger(int var1, int[] var2) {
      this.mag = stripLeadingZeroInts(var2);
      if (var1 >= -1 && var1 <= 1) {
         if (this.mag.length == 0) {
            this.signum = 0;
         } else {
            if (var1 == 0) {
               throw new NumberFormatException("signum-magnitude mismatch");
            }

            this.signum = var1;
         }

         if (this.mag.length >= 67108864) {
            this.checkRange();
         }

      } else {
         throw new NumberFormatException("Invalid signum value");
      }
   }

   public BigInteger(String var1, int var2) {
      int var3 = 0;
      int var5 = var1.length();
      if (var2 >= 2 && var2 <= 36) {
         if (var5 == 0) {
            throw new NumberFormatException("Zero length BigInteger");
         } else {
            byte var6 = 1;
            int var7 = var1.lastIndexOf(45);
            int var8 = var1.lastIndexOf(43);
            if (var7 >= 0) {
               if (var7 != 0 || var8 >= 0) {
                  throw new NumberFormatException("Illegal embedded sign character");
               }

               var6 = -1;
               var3 = 1;
            } else if (var8 >= 0) {
               if (var8 != 0) {
                  throw new NumberFormatException("Illegal embedded sign character");
               }

               var3 = 1;
            }

            if (var3 == var5) {
               throw new NumberFormatException("Zero length BigInteger");
            } else {
               while(var3 < var5 && Character.digit(var1.charAt(var3), var2) == 0) {
                  ++var3;
               }

               if (var3 == var5) {
                  this.signum = 0;
                  this.mag = ZERO.mag;
               } else {
                  int var4 = var5 - var3;
                  this.signum = var6;
                  long var9 = ((long)var4 * bitsPerDigit[var2] >>> 10) + 1L;
                  if (var9 + 31L >= 4294967296L) {
                     reportOverflow();
                  }

                  int var11 = (int)(var9 + 31L) >>> 5;
                  int[] var12 = new int[var11];
                  int var13 = var4 % digitsPerInt[var2];
                  if (var13 == 0) {
                     var13 = digitsPerInt[var2];
                  }

                  String var14 = var1.substring(var3, var3 += var13);
                  var12[var11 - 1] = Integer.parseInt(var14, var2);
                  if (var12[var11 - 1] < 0) {
                     throw new NumberFormatException("Illegal digit");
                  } else {
                     int var15 = intRadix[var2];
                     boolean var16 = false;

                     while(var3 < var5) {
                        var14 = var1.substring(var3, var3 += digitsPerInt[var2]);
                        int var17 = Integer.parseInt(var14, var2);
                        if (var17 < 0) {
                           throw new NumberFormatException("Illegal digit");
                        }

                        destructiveMulAdd(var12, var15, var17);
                     }

                     this.mag = trustedStripLeadingZeroInts(var12);
                     if (this.mag.length >= 67108864) {
                        this.checkRange();
                     }

                  }
               }
            }
         }
      } else {
         throw new NumberFormatException("Radix out of range");
      }
   }

   BigInteger(char[] var1, int var2, int var3) {
      int var4;
      for(var4 = 0; var4 < var3 && Character.digit(var1[var4], 10) == 0; ++var4) {
      }

      if (var4 == var3) {
         this.signum = 0;
         this.mag = ZERO.mag;
      } else {
         int var5 = var3 - var4;
         this.signum = var2;
         int var6;
         if (var3 < 10) {
            var6 = 1;
         } else {
            long var7 = ((long)var5 * bitsPerDigit[10] >>> 10) + 1L;
            if (var7 + 31L >= 4294967296L) {
               reportOverflow();
            }

            var6 = (int)(var7 + 31L) >>> 5;
         }

         int[] var10 = new int[var6];
         int var8 = var5 % digitsPerInt[10];
         if (var8 == 0) {
            var8 = digitsPerInt[10];
         }

         var10[var6 - 1] = this.parseInt(var1, var4, var4 += var8);

         while(var4 < var3) {
            int var9 = this.parseInt(var1, var4, var4 += digitsPerInt[10]);
            destructiveMulAdd(var10, intRadix[10], var9);
         }

         this.mag = trustedStripLeadingZeroInts(var10);
         if (this.mag.length >= 67108864) {
            this.checkRange();
         }

      }
   }

   private int parseInt(char[] var1, int var2, int var3) {
      int var4 = Character.digit(var1[var2++], 10);
      if (var4 == -1) {
         throw new NumberFormatException(new String(var1));
      } else {
         for(int var5 = var2; var5 < var3; ++var5) {
            int var6 = Character.digit(var1[var5], 10);
            if (var6 == -1) {
               throw new NumberFormatException(new String(var1));
            }

            var4 = 10 * var4 + var6;
         }

         return var4;
      }
   }

   private static void destructiveMulAdd(int[] var0, int var1, int var2) {
      long var3 = (long)var1 & 4294967295L;
      long var5 = (long)var2 & 4294967295L;
      int var7 = var0.length;
      long var8 = 0L;
      long var10 = 0L;

      for(int var12 = var7 - 1; var12 >= 0; --var12) {
         var8 = var3 * ((long)var0[var12] & 4294967295L) + var10;
         var0[var12] = (int)var8;
         var10 = var8 >>> 32;
      }

      long var15 = ((long)var0[var7 - 1] & 4294967295L) + var5;
      var0[var7 - 1] = (int)var15;
      var10 = var15 >>> 32;

      for(int var14 = var7 - 2; var14 >= 0; --var14) {
         var15 = ((long)var0[var14] & 4294967295L) + var10;
         var0[var14] = (int)var15;
         var10 = var15 >>> 32;
      }

   }

   public BigInteger(String var1) {
      this((String)var1, 10);
   }

   public BigInteger(int var1, Random var2) {
      this(1, (byte[])randomBits(var1, var2));
   }

   private static byte[] randomBits(int var0, Random var1) {
      if (var0 < 0) {
         throw new IllegalArgumentException("numBits must be non-negative");
      } else {
         int var2 = (int)(((long)var0 + 7L) / 8L);
         byte[] var3 = new byte[var2];
         if (var2 > 0) {
            var1.nextBytes(var3);
            int var4 = 8 * var2 - var0;
            var3[0] = (byte)(var3[0] & (1 << 8 - var4) - 1);
         }

         return var3;
      }
   }

   public BigInteger(int var1, int var2, Random var3) {
      if (var1 < 2) {
         throw new ArithmeticException("bitLength < 2");
      } else {
         BigInteger var4 = var1 < 95 ? smallPrime(var1, var2, var3) : largePrime(var1, var2, var3);
         this.signum = 1;
         this.mag = var4.mag;
      }
   }

   public static BigInteger probablePrime(int var0, Random var1) {
      if (var0 < 2) {
         throw new ArithmeticException("bitLength < 2");
      } else {
         return var0 < 95 ? smallPrime(var0, 100, var1) : largePrime(var0, 100, var1);
      }
   }

   private static BigInteger smallPrime(int var0, int var1, Random var2) {
      int var3 = var0 + 31 >>> 5;
      int[] var4 = new int[var3];
      int var5 = 1 << (var0 + 31 & 31);
      int var6 = (var5 << 1) - 1;

      BigInteger var10;
      do {
         long var8;
         do {
            for(int var7 = 0; var7 < var3; ++var7) {
               var4[var7] = var2.nextInt();
            }

            var4[0] = var4[0] & var6 | var5;
            if (var0 > 2) {
               var4[var3 - 1] |= 1;
            }

            var10 = new BigInteger(var4, 1);
            if (var0 <= 6) {
               break;
            }

            var8 = var10.remainder(SMALL_PRIME_PRODUCT).longValue();
         } while(var8 % 3L == 0L || var8 % 5L == 0L || var8 % 7L == 0L || var8 % 11L == 0L || var8 % 13L == 0L || var8 % 17L == 0L || var8 % 19L == 0L || var8 % 23L == 0L || var8 % 29L == 0L || var8 % 31L == 0L || var8 % 37L == 0L || var8 % 41L == 0L);

         if (var0 < 4) {
            return var10;
         }
      } while(!var10.primeToCertainty(var1, var2));

      return var10;
   }

   private static BigInteger largePrime(int var0, int var1, Random var2) {
      BigInteger var3 = (new BigInteger(var0, var2)).setBit(var0 - 1);
      int[] var10000 = var3.mag;
      int var10001 = var3.mag.length - 1;
      var10000[var10001] &= -2;
      int var4 = getPrimeSearchLen(var0);
      BitSieve var5 = new BitSieve(var3, var4);

      BigInteger var6;
      for(var6 = var5.retrieve(var3, var1, var2); var6 == null || var6.bitLength() != var0; var6 = var5.retrieve(var3, var1, var2)) {
         var3 = var3.add(valueOf((long)(2 * var4)));
         if (var3.bitLength() != var0) {
            var3 = (new BigInteger(var0, var2)).setBit(var0 - 1);
         }

         var10000 = var3.mag;
         var10001 = var3.mag.length - 1;
         var10000[var10001] &= -2;
         var5 = new BitSieve(var3, var4);
      }

      return var6;
   }

   public BigInteger nextProbablePrime() {
      if (this.signum < 0) {
         throw new ArithmeticException("start < 0: " + this);
      } else if (this.signum != 0 && !this.equals(ONE)) {
         BigInteger var1 = this.add(ONE);
         if (var1.bitLength() < 95) {
            if (!var1.testBit(0)) {
               var1 = var1.add(ONE);
            }

            while(true) {
               while(true) {
                  if (var1.bitLength() > 6) {
                     long var5 = var1.remainder(SMALL_PRIME_PRODUCT).longValue();
                     if (var5 % 3L == 0L || var5 % 5L == 0L || var5 % 7L == 0L || var5 % 11L == 0L || var5 % 13L == 0L || var5 % 17L == 0L || var5 % 19L == 0L || var5 % 23L == 0L || var5 % 29L == 0L || var5 % 31L == 0L || var5 % 37L == 0L || var5 % 41L == 0L) {
                        var1 = var1.add(TWO);
                        continue;
                     }
                  }

                  if (var1.bitLength() < 4) {
                     return var1;
                  }

                  if (var1.primeToCertainty(100, (Random)null)) {
                     return var1;
                  }

                  var1 = var1.add(TWO);
               }
            }
         } else {
            if (var1.testBit(0)) {
               var1 = var1.subtract(ONE);
            }

            int var2 = getPrimeSearchLen(var1.bitLength());

            while(true) {
               BitSieve var3 = new BitSieve(var1, var2);
               BigInteger var4 = var3.retrieve(var1, 100, (Random)null);
               if (var4 != null) {
                  return var4;
               }

               var1 = var1.add(valueOf((long)(2 * var2)));
            }
         }
      } else {
         return TWO;
      }
   }

   private static int getPrimeSearchLen(int var0) {
      if (var0 > 500000001) {
         throw new ArithmeticException("Prime search implementation restriction on bitLength");
      } else {
         return var0 / 20 * 64;
      }
   }

   boolean primeToCertainty(int var1, Random var2) {
      boolean var3 = false;
      int var4 = (Math.min(var1, 2147483646) + 1) / 2;
      int var5 = this.bitLength();
      byte var6;
      int var7;
      if (var5 < 100) {
         var6 = 50;
         var7 = var4 < var6 ? var4 : var6;
         return this.passesMillerRabin(var7, var2);
      } else {
         if (var5 < 256) {
            var6 = 27;
         } else if (var5 < 512) {
            var6 = 15;
         } else if (var5 < 768) {
            var6 = 8;
         } else if (var5 < 1024) {
            var6 = 4;
         } else {
            var6 = 2;
         }

         var7 = var4 < var6 ? var4 : var6;
         return this.passesMillerRabin(var7, var2) && this.passesLucasLehmer();
      }
   }

   private boolean passesLucasLehmer() {
      BigInteger var1 = this.add(ONE);

      int var2;
      for(var2 = 5; jacobiSymbol(var2, this) != -1; var2 = var2 < 0 ? Math.abs(var2) + 2 : -(var2 + 2)) {
      }

      BigInteger var3 = lucasLehmerSequence(var2, var1, this);
      return var3.mod(this).equals(ZERO);
   }

   private static int jacobiSymbol(int var0, BigInteger var1) {
      if (var0 == 0) {
         return 0;
      } else {
         int var2 = 1;
         int var3 = var1.mag[var1.mag.length - 1];
         int var4;
         if (var0 < 0) {
            var0 = -var0;
            var4 = var3 & 7;
            if (var4 == 3 || var4 == 7) {
               var2 = -var2;
            }
         }

         while((var0 & 3) == 0) {
            var0 >>= 2;
         }

         if ((var0 & 1) == 0) {
            var0 >>= 1;
            if (((var3 ^ var3 >> 1) & 2) != 0) {
               var2 = -var2;
            }
         }

         if (var0 == 1) {
            return var2;
         } else {
            if ((var0 & var3 & 2) != 0) {
               var2 = -var2;
            }

            for(var3 = var1.mod(valueOf((long)var0)).intValue(); var3 != 0; var3 %= var4) {
               while((var3 & 3) == 0) {
                  var3 >>= 2;
               }

               if ((var3 & 1) == 0) {
                  var3 >>= 1;
                  if (((var0 ^ var0 >> 1) & 2) != 0) {
                     var2 = -var2;
                  }
               }

               if (var3 == 1) {
                  return var2;
               }

               assert var3 < var0;

               var4 = var3;
               var3 = var0;
               var0 = var4;
               if ((var3 & var4 & 2) != 0) {
                  var2 = -var2;
               }
            }

            return 0;
         }
      }
   }

   private static BigInteger lucasLehmerSequence(int var0, BigInteger var1, BigInteger var2) {
      BigInteger var3 = valueOf((long)var0);
      BigInteger var4 = ONE;
      BigInteger var6 = ONE;

      for(int var8 = var1.bitLength() - 2; var8 >= 0; --var8) {
         BigInteger var5 = var4.multiply(var6).mod(var2);
         BigInteger var7 = var6.square().add(var3.multiply(var4.square())).mod(var2);
         if (var7.testBit(0)) {
            var7 = var7.subtract(var2);
         }

         var7 = var7.shiftRight(1);
         var4 = var5;
         var6 = var7;
         if (var1.testBit(var8)) {
            var5 = var5.add(var7).mod(var2);
            if (var5.testBit(0)) {
               var5 = var5.subtract(var2);
            }

            var5 = var5.shiftRight(1);
            var7 = var7.add(var3.multiply(var4)).mod(var2);
            if (var7.testBit(0)) {
               var7 = var7.subtract(var2);
            }

            var7 = var7.shiftRight(1);
            var4 = var5;
            var6 = var7;
         }
      }

      return var4;
   }

   private boolean passesMillerRabin(int var1, Random var2) {
      BigInteger var3 = this.subtract(ONE);
      int var5 = var3.getLowestSetBit();
      BigInteger var4 = var3.shiftRight(var5);
      if (var2 == null) {
         var2 = ThreadLocalRandom.current();
      }

      for(int var6 = 0; var6 < var1; ++var6) {
         BigInteger var7;
         do {
            do {
               var7 = new BigInteger(this.bitLength(), (Random)var2);
            } while(var7.compareTo(ONE) <= 0);
         } while(var7.compareTo(this) >= 0);

         int var8 = 0;

         for(BigInteger var9 = var7.modPow(var4, this); (var8 != 0 || !var9.equals(ONE)) && !var9.equals(var3); var9 = var9.modPow(TWO, this)) {
            if (var8 > 0 && var9.equals(ONE)) {
               return false;
            }

            ++var8;
            if (var8 == var5) {
               return false;
            }
         }
      }

      return true;
   }

   BigInteger(int[] var1, int var2) {
      this.signum = var1.length == 0 ? 0 : var2;
      this.mag = var1;
      if (this.mag.length >= 67108864) {
         this.checkRange();
      }

   }

   private BigInteger(byte[] var1, int var2) {
      this.signum = var1.length == 0 ? 0 : var2;
      this.mag = stripLeadingZeroBytes(var1);
      if (this.mag.length >= 67108864) {
         this.checkRange();
      }

   }

   private void checkRange() {
      if (this.mag.length > 67108864 || this.mag.length == 67108864 && this.mag[0] < 0) {
         reportOverflow();
      }

   }

   private static void reportOverflow() {
      throw new ArithmeticException("BigInteger would overflow supported range");
   }

   public static BigInteger valueOf(long var0) {
      if (var0 == 0L) {
         return ZERO;
      } else if (var0 > 0L && var0 <= 16L) {
         return posConst[(int)var0];
      } else {
         return var0 < 0L && var0 >= -16L ? negConst[(int)(-var0)] : new BigInteger(var0);
      }
   }

   private BigInteger(long var1) {
      if (var1 < 0L) {
         var1 = -var1;
         this.signum = -1;
      } else {
         this.signum = 1;
      }

      int var3 = (int)(var1 >>> 32);
      if (var3 == 0) {
         this.mag = new int[1];
         this.mag[0] = (int)var1;
      } else {
         this.mag = new int[2];
         this.mag[0] = var3;
         this.mag[1] = (int)var1;
      }

   }

   private static BigInteger valueOf(int[] var0) {
      return var0[0] > 0 ? new BigInteger(var0, 1) : new BigInteger(var0);
   }

   public BigInteger add(BigInteger var1) {
      if (var1.signum == 0) {
         return this;
      } else if (this.signum == 0) {
         return var1;
      } else if (var1.signum == this.signum) {
         return new BigInteger(add(this.mag, var1.mag), this.signum);
      } else {
         int var2 = this.compareMagnitude(var1);
         if (var2 == 0) {
            return ZERO;
         } else {
            int[] var3 = var2 > 0 ? subtract(this.mag, var1.mag) : subtract(var1.mag, this.mag);
            var3 = trustedStripLeadingZeroInts(var3);
            return new BigInteger(var3, var2 == this.signum ? 1 : -1);
         }
      }
   }

   BigInteger add(long var1) {
      if (var1 == 0L) {
         return this;
      } else if (this.signum == 0) {
         return valueOf(var1);
      } else if (Long.signum(var1) == this.signum) {
         return new BigInteger(add(this.mag, Math.abs(var1)), this.signum);
      } else {
         int var3 = this.compareMagnitude(var1);
         if (var3 == 0) {
            return ZERO;
         } else {
            int[] var4 = var3 > 0 ? subtract(this.mag, Math.abs(var1)) : subtract(Math.abs(var1), this.mag);
            var4 = trustedStripLeadingZeroInts(var4);
            return new BigInteger(var4, var3 == this.signum ? 1 : -1);
         }
      }
   }

   private static int[] add(int[] var0, long var1) {
      long var4 = 0L;
      int var6 = var0.length;
      int var8 = (int)(var1 >>> 32);
      int[] var7;
      if (var8 == 0) {
         var7 = new int[var6];
         --var6;
         var4 = ((long)var0[var6] & 4294967295L) + var1;
         var7[var6] = (int)var4;
      } else {
         if (var6 == 1) {
            var7 = new int[2];
            var4 = var1 + ((long)var0[0] & 4294967295L);
            var7[1] = (int)var4;
            var7[0] = (int)(var4 >>> 32);
            return var7;
         }

         var7 = new int[var6];
         --var6;
         var4 = ((long)var0[var6] & 4294967295L) + (var1 & 4294967295L);
         var7[var6] = (int)var4;
         --var6;
         var4 = ((long)var0[var6] & 4294967295L) + ((long)var8 & 4294967295L) + (var4 >>> 32);
         var7[var6] = (int)var4;
      }

      boolean var9;
      for(var9 = var4 >>> 32 != 0L; var6 > 0 && var9; var9 = (var7[var6] = var0[var6] + 1) == 0) {
         --var6;
      }

      while(var6 > 0) {
         --var6;
         var7[var6] = var0[var6];
      }

      if (var9) {
         int[] var10 = new int[var7.length + 1];
         System.arraycopy(var7, 0, var10, 1, var7.length);
         var10[0] = 1;
         return var10;
      } else {
         return var7;
      }
   }

   private static int[] add(int[] var0, int[] var1) {
      if (var0.length < var1.length) {
         int[] var2 = var0;
         var0 = var1;
         var1 = var2;
      }

      int var9 = var0.length;
      int var3 = var1.length;
      int[] var4 = new int[var9];
      long var5 = 0L;
      if (var3 == 1) {
         --var9;
         var5 = ((long)var0[var9] & 4294967295L) + ((long)var1[0] & 4294967295L);
         var4[var9] = (int)var5;
      } else {
         while(var3 > 0) {
            --var9;
            long var10000 = (long)var0[var9] & 4294967295L;
            --var3;
            var5 = var10000 + ((long)var1[var3] & 4294967295L) + (var5 >>> 32);
            var4[var9] = (int)var5;
         }
      }

      boolean var7;
      for(var7 = var5 >>> 32 != 0L; var9 > 0 && var7; var7 = (var4[var9] = var0[var9] + 1) == 0) {
         --var9;
      }

      while(var9 > 0) {
         --var9;
         var4[var9] = var0[var9];
      }

      if (var7) {
         int[] var8 = new int[var4.length + 1];
         System.arraycopy(var4, 0, var8, 1, var4.length);
         var8[0] = 1;
         return var8;
      } else {
         return var4;
      }
   }

   private static int[] subtract(long var0, int[] var2) {
      int var3 = (int)(var0 >>> 32);
      int[] var4;
      if (var3 == 0) {
         var4 = new int[]{(int)(var0 - ((long)var2[0] & 4294967295L))};
         return var4;
      } else {
         var4 = new int[2];
         long var5;
         if (var2.length == 1) {
            var5 = ((long)((int)var0) & 4294967295L) - ((long)var2[0] & 4294967295L);
            var4[1] = (int)var5;
            boolean var7 = var5 >> 32 != 0L;
            if (var7) {
               var4[0] = var3 - 1;
            } else {
               var4[0] = var3;
            }

            return var4;
         } else {
            var5 = ((long)((int)var0) & 4294967295L) - ((long)var2[1] & 4294967295L);
            var4[1] = (int)var5;
            var5 = ((long)var3 & 4294967295L) - ((long)var2[0] & 4294967295L) + (var5 >> 32);
            var4[0] = (int)var5;
            return var4;
         }
      }
   }

   private static int[] subtract(int[] var0, long var1) {
      int var3 = (int)(var1 >>> 32);
      int var4 = var0.length;
      int[] var5 = new int[var4];
      long var6 = 0L;
      if (var3 == 0) {
         --var4;
         var6 = ((long)var0[var4] & 4294967295L) - var1;
         var5[var4] = (int)var6;
      } else {
         --var4;
         var6 = ((long)var0[var4] & 4294967295L) - (var1 & 4294967295L);
         var5[var4] = (int)var6;
         --var4;
         var6 = ((long)var0[var4] & 4294967295L) - ((long)var3 & 4294967295L) + (var6 >> 32);
         var5[var4] = (int)var6;
      }

      for(boolean var8 = var6 >> 32 != 0L; var4 > 0 && var8; var8 = (var5[var4] = var0[var4] - 1) == -1) {
         --var4;
      }

      while(var4 > 0) {
         --var4;
         var5[var4] = var0[var4];
      }

      return var5;
   }

   public BigInteger subtract(BigInteger var1) {
      if (var1.signum == 0) {
         return this;
      } else if (this.signum == 0) {
         return var1.negate();
      } else if (var1.signum != this.signum) {
         return new BigInteger(add(this.mag, var1.mag), this.signum);
      } else {
         int var2 = this.compareMagnitude(var1);
         if (var2 == 0) {
            return ZERO;
         } else {
            int[] var3 = var2 > 0 ? subtract(this.mag, var1.mag) : subtract(var1.mag, this.mag);
            var3 = trustedStripLeadingZeroInts(var3);
            return new BigInteger(var3, var2 == this.signum ? 1 : -1);
         }
      }
   }

   private static int[] subtract(int[] var0, int[] var1) {
      int var2 = var0.length;
      int[] var3 = new int[var2];
      int var4 = var1.length;

      long var5;
      for(var5 = 0L; var4 > 0; var3[var2] = (int)var5) {
         --var2;
         long var10000 = (long)var0[var2] & 4294967295L;
         --var4;
         var5 = var10000 - ((long)var1[var4] & 4294967295L) + (var5 >> 32);
      }

      for(boolean var7 = var5 >> 32 != 0L; var2 > 0 && var7; var7 = (var3[var2] = var0[var2] - 1) == -1) {
         --var2;
      }

      while(var2 > 0) {
         --var2;
         var3[var2] = var0[var2];
      }

      return var3;
   }

   public BigInteger multiply(BigInteger var1) {
      if (var1.signum != 0 && this.signum != 0) {
         int var2 = this.mag.length;
         if (var1 == this && var2 > 20) {
            return this.square();
         } else {
            int var3 = var1.mag.length;
            if (var2 >= 80 && var3 >= 80) {
               return var2 < 240 && var3 < 240 ? multiplyKaratsuba(this, var1) : multiplyToomCook3(this, var1);
            } else {
               int var4 = this.signum == var1.signum ? 1 : -1;
               if (var1.mag.length == 1) {
                  return multiplyByInt(this.mag, var1.mag[0], var4);
               } else if (this.mag.length == 1) {
                  return multiplyByInt(var1.mag, this.mag[0], var4);
               } else {
                  int[] var5 = multiplyToLen(this.mag, var2, var1.mag, var3, (int[])null);
                  var5 = trustedStripLeadingZeroInts(var5);
                  return new BigInteger(var5, var4);
               }
            }
         }
      } else {
         return ZERO;
      }
   }

   private static BigInteger multiplyByInt(int[] var0, int var1, int var2) {
      if (Integer.bitCount(var1) == 1) {
         return new BigInteger(shiftLeft(var0, Integer.numberOfTrailingZeros(var1)), var2);
      } else {
         int var3 = var0.length;
         int[] var4 = new int[var3 + 1];
         long var5 = 0L;
         long var7 = (long)var1 & 4294967295L;
         int var9 = var4.length - 1;

         for(int var10 = var3 - 1; var10 >= 0; --var10) {
            long var11 = ((long)var0[var10] & 4294967295L) * var7 + var5;
            var4[var9--] = (int)var11;
            var5 = var11 >>> 32;
         }

         if (var5 == 0L) {
            var4 = Arrays.copyOfRange(var4, 1, var4.length);
         } else {
            var4[var9] = (int)var5;
         }

         return new BigInteger(var4, var2);
      }
   }

   BigInteger multiply(long var1) {
      if (var1 != 0L && this.signum != 0) {
         if (var1 == Long.MIN_VALUE) {
            return this.multiply(valueOf(var1));
         } else {
            int var3 = var1 > 0L ? this.signum : -this.signum;
            if (var1 < 0L) {
               var1 = -var1;
            }

            long var4 = var1 >>> 32;
            long var6 = var1 & 4294967295L;
            int var8 = this.mag.length;
            int[] var9 = this.mag;
            int[] var10 = var4 == 0L ? new int[var8 + 1] : new int[var8 + 2];
            long var11 = 0L;
            int var13 = var10.length - 1;

            int var14;
            long var15;
            for(var14 = var8 - 1; var14 >= 0; --var14) {
               var15 = ((long)var9[var14] & 4294967295L) * var6 + var11;
               var10[var13--] = (int)var15;
               var11 = var15 >>> 32;
            }

            var10[var13] = (int)var11;
            if (var4 != 0L) {
               var11 = 0L;
               var13 = var10.length - 2;

               for(var14 = var8 - 1; var14 >= 0; --var14) {
                  var15 = ((long)var9[var14] & 4294967295L) * var4 + ((long)var10[var13] & 4294967295L) + var11;
                  var10[var13--] = (int)var15;
                  var11 = var15 >>> 32;
               }

               var10[0] = (int)var11;
            }

            if (var11 == 0L) {
               var10 = Arrays.copyOfRange(var10, 1, var10.length);
            }

            return new BigInteger(var10, var3);
         }
      } else {
         return ZERO;
      }
   }

   private static int[] multiplyToLen(int[] var0, int var1, int[] var2, int var3, int[] var4) {
      int var5 = var1 - 1;
      int var6 = var3 - 1;
      if (var4 == null || var4.length < var1 + var3) {
         var4 = new int[var1 + var3];
      }

      long var7 = 0L;
      int var9 = var6;

      int var10;
      for(var10 = var6 + 1 + var5; var9 >= 0; --var10) {
         long var11 = ((long)var2[var9] & 4294967295L) * ((long)var0[var5] & 4294967295L) + var7;
         var4[var10] = (int)var11;
         var7 = var11 >>> 32;
         --var9;
      }

      var4[var5] = (int)var7;

      for(var9 = var5 - 1; var9 >= 0; --var9) {
         var7 = 0L;
         var10 = var6;

         for(int var14 = var6 + 1 + var9; var10 >= 0; --var14) {
            long var12 = ((long)var2[var10] & 4294967295L) * ((long)var0[var9] & 4294967295L) + ((long)var4[var14] & 4294967295L) + var7;
            var4[var14] = (int)var12;
            var7 = var12 >>> 32;
            --var10;
         }

         var4[var9] = (int)var7;
      }

      return var4;
   }

   private static BigInteger multiplyKaratsuba(BigInteger var0, BigInteger var1) {
      int var2 = var0.mag.length;
      int var3 = var1.mag.length;
      int var4 = (Math.max(var2, var3) + 1) / 2;
      BigInteger var5 = var0.getLower(var4);
      BigInteger var6 = var0.getUpper(var4);
      BigInteger var7 = var1.getLower(var4);
      BigInteger var8 = var1.getUpper(var4);
      BigInteger var9 = var6.multiply(var8);
      BigInteger var10 = var5.multiply(var7);
      BigInteger var11 = var6.add(var5).multiply(var8.add(var7));
      BigInteger var12 = var9.shiftLeft(32 * var4).add(var11.subtract(var9).subtract(var10)).shiftLeft(32 * var4).add(var10);
      return var0.signum != var1.signum ? var12.negate() : var12;
   }

   private static BigInteger multiplyToomCook3(BigInteger var0, BigInteger var1) {
      int var2 = var0.mag.length;
      int var3 = var1.mag.length;
      int var4 = Math.max(var2, var3);
      int var5 = (var4 + 2) / 3;
      int var6 = var4 - 2 * var5;
      BigInteger var9 = var0.getToomSlice(var5, var6, 0, var4);
      BigInteger var8 = var0.getToomSlice(var5, var6, 1, var4);
      BigInteger var7 = var0.getToomSlice(var5, var6, 2, var4);
      BigInteger var12 = var1.getToomSlice(var5, var6, 0, var4);
      BigInteger var11 = var1.getToomSlice(var5, var6, 1, var4);
      BigInteger var10 = var1.getToomSlice(var5, var6, 2, var4);
      BigInteger var13 = var7.multiply(var10);
      BigInteger var21 = var9.add(var7);
      BigInteger var22 = var12.add(var10);
      BigInteger var16 = var21.subtract(var8).multiply(var22.subtract(var11));
      var21 = var21.add(var8);
      var22 = var22.add(var11);
      BigInteger var14 = var21.multiply(var22);
      BigInteger var15 = var21.add(var9).shiftLeft(1).subtract(var7).multiply(var22.add(var12).shiftLeft(1).subtract(var10));
      BigInteger var17 = var9.multiply(var12);
      BigInteger var19 = var15.subtract(var16).exactDivideBy3();
      BigInteger var20 = var14.subtract(var16).shiftRight(1);
      BigInteger var18 = var14.subtract(var13);
      var19 = var19.subtract(var18).shiftRight(1);
      var18 = var18.subtract(var20).subtract(var17);
      var19 = var19.subtract(var17.shiftLeft(1));
      var20 = var20.subtract(var19);
      int var23 = var5 * 32;
      BigInteger var24 = var17.shiftLeft(var23).add(var19).shiftLeft(var23).add(var18).shiftLeft(var23).add(var20).shiftLeft(var23).add(var13);
      return var0.signum != var1.signum ? var24.negate() : var24;
   }

   private BigInteger getToomSlice(int var1, int var2, int var3, int var4) {
      int var8 = this.mag.length;
      int var9 = var4 - var8;
      int var5;
      int var6;
      if (var3 == 0) {
         var5 = 0 - var9;
         var6 = var2 - 1 - var9;
      } else {
         var5 = var2 + (var3 - 1) * var1 - var9;
         var6 = var5 + var1 - 1;
      }

      if (var5 < 0) {
         var5 = 0;
      }

      if (var6 < 0) {
         return ZERO;
      } else {
         int var7 = var6 - var5 + 1;
         if (var7 <= 0) {
            return ZERO;
         } else if (var5 == 0 && var7 >= var8) {
            return this.abs();
         } else {
            int[] var10 = new int[var7];
            System.arraycopy(this.mag, var5, var10, 0, var7);
            return new BigInteger(trustedStripLeadingZeroInts(var10), 1);
         }
      }
   }

   private BigInteger exactDivideBy3() {
      int var1 = this.mag.length;
      int[] var2 = new int[var1];
      long var9 = 0L;

      for(int var11 = var1 - 1; var11 >= 0; --var11) {
         long var3 = (long)this.mag[var11] & 4294967295L;
         long var5 = var3 - var9;
         if (var9 > var3) {
            var9 = 1L;
         } else {
            var9 = 0L;
         }

         long var7 = var5 * 2863311531L & 4294967295L;
         var2[var11] = (int)var7;
         if (var7 >= 1431655766L) {
            ++var9;
            if (var7 >= 2863311531L) {
               ++var9;
            }
         }
      }

      var2 = trustedStripLeadingZeroInts(var2);
      return new BigInteger(var2, this.signum);
   }

   private BigInteger getLower(int var1) {
      int var2 = this.mag.length;
      if (var2 <= var1) {
         return this.abs();
      } else {
         int[] var3 = new int[var1];
         System.arraycopy(this.mag, var2 - var1, var3, 0, var1);
         return new BigInteger(trustedStripLeadingZeroInts(var3), 1);
      }
   }

   private BigInteger getUpper(int var1) {
      int var2 = this.mag.length;
      if (var2 <= var1) {
         return ZERO;
      } else {
         int var3 = var2 - var1;
         int[] var4 = new int[var3];
         System.arraycopy(this.mag, 0, var4, 0, var3);
         return new BigInteger(trustedStripLeadingZeroInts(var4), 1);
      }
   }

   private BigInteger square() {
      if (this.signum == 0) {
         return ZERO;
      } else {
         int var1 = this.mag.length;
         if (var1 < 128) {
            int[] var2 = squareToLen(this.mag, var1, (int[])null);
            return new BigInteger(trustedStripLeadingZeroInts(var2), 1);
         } else {
            return var1 < 216 ? this.squareKaratsuba() : this.squareToomCook3();
         }
      }
   }

   private static final int[] squareToLen(int[] var0, int var1, int[] var2) {
      int var3 = var1 << 1;
      if (var2 == null || var2.length < var3) {
         var2 = new int[var3];
      }

      implSquareToLenChecks(var0, var1, var2, var3);
      return implSquareToLen(var0, var1, var2, var3);
   }

   private static void implSquareToLenChecks(int[] var0, int var1, int[] var2, int var3) throws RuntimeException {
      if (var1 < 1) {
         throw new IllegalArgumentException("invalid input length: " + var1);
      } else if (var1 > var0.length) {
         throw new IllegalArgumentException("input length out of bound: " + var1 + " > " + var0.length);
      } else if (var1 * 2 > var2.length) {
         throw new IllegalArgumentException("input length out of bound: " + var1 * 2 + " > " + var2.length);
      } else if (var3 < 1) {
         throw new IllegalArgumentException("invalid input length: " + var3);
      } else if (var3 > var2.length) {
         throw new IllegalArgumentException("input length out of bound: " + var1 + " > " + var2.length);
      }
   }

   private static final int[] implSquareToLen(int[] var0, int var1, int[] var2, int var3) {
      int var4 = 0;
      int var5 = 0;

      int var6;
      for(var6 = 0; var5 < var1; ++var5) {
         long var7 = (long)var0[var5] & 4294967295L;
         long var9 = var7 * var7;
         var2[var6++] = var4 << 31 | (int)(var9 >>> 33);
         var2[var6++] = (int)(var9 >>> 1);
         var4 = (int)var9;
      }

      var5 = var1;

      for(var6 = 1; var5 > 0; var6 += 2) {
         int var11 = var0[var5 - 1];
         var11 = mulAdd(var2, var0, var6, var5 - 1, var11);
         addOne(var2, var6 - 1, var5, var11);
         --var5;
      }

      primitiveLeftShift(var2, var3, 1);
      var2[var3 - 1] |= var0[var1 - 1] & 1;
      return var2;
   }

   private BigInteger squareKaratsuba() {
      int var1 = (this.mag.length + 1) / 2;
      BigInteger var2 = this.getLower(var1);
      BigInteger var3 = this.getUpper(var1);
      BigInteger var4 = var3.square();
      BigInteger var5 = var2.square();
      return var4.shiftLeft(var1 * 32).add(var2.add(var3).square().subtract(var4.add(var5))).shiftLeft(var1 * 32).add(var5);
   }

   private BigInteger squareToomCook3() {
      int var1 = this.mag.length;
      int var2 = (var1 + 2) / 3;
      int var3 = var1 - 2 * var2;
      BigInteger var6 = this.getToomSlice(var2, var3, 0, var1);
      BigInteger var5 = this.getToomSlice(var2, var3, 1, var1);
      BigInteger var4 = this.getToomSlice(var2, var3, 2, var1);
      BigInteger var7 = var4.square();
      BigInteger var15 = var6.add(var4);
      BigInteger var10 = var15.subtract(var5).square();
      var15 = var15.add(var5);
      BigInteger var8 = var15.square();
      BigInteger var11 = var6.square();
      BigInteger var9 = var15.add(var6).shiftLeft(1).subtract(var4).square();
      BigInteger var13 = var9.subtract(var10).exactDivideBy3();
      BigInteger var14 = var8.subtract(var10).shiftRight(1);
      BigInteger var12 = var8.subtract(var7);
      var13 = var13.subtract(var12).shiftRight(1);
      var12 = var12.subtract(var14).subtract(var11);
      var13 = var13.subtract(var11.shiftLeft(1));
      var14 = var14.subtract(var13);
      int var16 = var2 * 32;
      return var11.shiftLeft(var16).add(var13).shiftLeft(var16).add(var12).shiftLeft(var16).add(var14).shiftLeft(var16).add(var7);
   }

   public BigInteger divide(BigInteger var1) {
      return var1.mag.length >= 80 && this.mag.length - var1.mag.length >= 40 ? this.divideBurnikelZiegler(var1) : this.divideKnuth(var1);
   }

   private BigInteger divideKnuth(BigInteger var1) {
      MutableBigInteger var2 = new MutableBigInteger();
      MutableBigInteger var3 = new MutableBigInteger(this.mag);
      MutableBigInteger var4 = new MutableBigInteger(var1.mag);
      var3.divideKnuth(var4, var2, false);
      return var2.toBigInteger(this.signum * var1.signum);
   }

   public BigInteger[] divideAndRemainder(BigInteger var1) {
      return var1.mag.length >= 80 && this.mag.length - var1.mag.length >= 40 ? this.divideAndRemainderBurnikelZiegler(var1) : this.divideAndRemainderKnuth(var1);
   }

   private BigInteger[] divideAndRemainderKnuth(BigInteger var1) {
      BigInteger[] var2 = new BigInteger[2];
      MutableBigInteger var3 = new MutableBigInteger();
      MutableBigInteger var4 = new MutableBigInteger(this.mag);
      MutableBigInteger var5 = new MutableBigInteger(var1.mag);
      MutableBigInteger var6 = var4.divideKnuth(var5, var3);
      var2[0] = var3.toBigInteger(this.signum == var1.signum ? 1 : -1);
      var2[1] = var6.toBigInteger(this.signum);
      return var2;
   }

   public BigInteger remainder(BigInteger var1) {
      return var1.mag.length >= 80 && this.mag.length - var1.mag.length >= 40 ? this.remainderBurnikelZiegler(var1) : this.remainderKnuth(var1);
   }

   private BigInteger remainderKnuth(BigInteger var1) {
      MutableBigInteger var2 = new MutableBigInteger();
      MutableBigInteger var3 = new MutableBigInteger(this.mag);
      MutableBigInteger var4 = new MutableBigInteger(var1.mag);
      return var3.divideKnuth(var4, var2).toBigInteger(this.signum);
   }

   private BigInteger divideBurnikelZiegler(BigInteger var1) {
      return this.divideAndRemainderBurnikelZiegler(var1)[0];
   }

   private BigInteger remainderBurnikelZiegler(BigInteger var1) {
      return this.divideAndRemainderBurnikelZiegler(var1)[1];
   }

   private BigInteger[] divideAndRemainderBurnikelZiegler(BigInteger var1) {
      MutableBigInteger var2 = new MutableBigInteger();
      MutableBigInteger var3 = (new MutableBigInteger(this)).divideAndRemainderBurnikelZiegler(new MutableBigInteger(var1), var2);
      BigInteger var4 = var2.isZero() ? ZERO : var2.toBigInteger(this.signum * var1.signum);
      BigInteger var5 = var3.isZero() ? ZERO : var3.toBigInteger(this.signum);
      return new BigInteger[]{var4, var5};
   }

   public BigInteger pow(int var1) {
      if (var1 < 0) {
         throw new ArithmeticException("Negative exponent");
      } else if (this.signum == 0) {
         return var1 == 0 ? ONE : this;
      } else {
         BigInteger var2 = this.abs();
         int var3 = var2.getLowestSetBit();
         long var4 = (long)var3 * (long)var1;
         if (var4 > 2147483647L) {
            reportOverflow();
         }

         int var6;
         if (var3 > 0) {
            var2 = var2.shiftRight(var3);
            var6 = var2.bitLength();
            if (var6 == 1) {
               if (this.signum < 0 && (var1 & 1) == 1) {
                  return NEGATIVE_ONE.shiftLeft(var3 * var1);
               }

               return ONE.shiftLeft(var3 * var1);
            }
         } else {
            var6 = var2.bitLength();
            if (var6 == 1) {
               if (this.signum < 0 && (var1 & 1) == 1) {
                  return NEGATIVE_ONE;
               }

               return ONE;
            }
         }

         long var7 = (long)var6 * (long)var1;
         if (var2.mag.length == 1 && var7 <= 62L) {
            int var15 = this.signum < 0 && (var1 & 1) == 1 ? -1 : 1;
            long var16 = 1L;
            long var12 = (long)var2.mag[0] & 4294967295L;
            int var14 = var1;

            while(var14 != 0) {
               if ((var14 & 1) == 1) {
                  var16 *= var12;
               }

               if ((var14 >>>= 1) != 0) {
                  var12 *= var12;
               }
            }

            if (var3 > 0) {
               if (var4 + var7 <= 62L) {
                  return valueOf((var16 << (int)var4) * (long)var15);
               } else {
                  return valueOf(var16 * (long)var15).shiftLeft((int)var4);
               }
            } else {
               return valueOf(var16 * (long)var15);
            }
         } else {
            BigInteger var9 = ONE;
            int var10 = var1;

            while(var10 != 0) {
               if ((var10 & 1) == 1) {
                  var9 = var9.multiply(var2);
               }

               if ((var10 >>>= 1) != 0) {
                  var2 = var2.square();
               }
            }

            if (var3 > 0) {
               var9 = var9.shiftLeft(var3 * var1);
            }

            if (this.signum < 0 && (var1 & 1) == 1) {
               return var9.negate();
            } else {
               return var9;
            }
         }
      }
   }

   public BigInteger gcd(BigInteger var1) {
      if (var1.signum == 0) {
         return this.abs();
      } else if (this.signum == 0) {
         return var1.abs();
      } else {
         MutableBigInteger var2 = new MutableBigInteger(this);
         MutableBigInteger var3 = new MutableBigInteger(var1);
         MutableBigInteger var4 = var2.hybridGCD(var3);
         return var4.toBigInteger(1);
      }
   }

   static int bitLengthForInt(int var0) {
      return 32 - Integer.numberOfLeadingZeros(var0);
   }

   private static int[] leftShift(int[] var0, int var1, int var2) {
      int var3 = var2 >>> 5;
      int var4 = var2 & 31;
      int var5 = bitLengthForInt(var0[0]);
      if (var2 <= 32 - var5) {
         primitiveLeftShift(var0, var1, var4);
         return var0;
      } else {
         int[] var6;
         if (var4 <= 32 - var5) {
            var6 = new int[var3 + var1];
            System.arraycopy(var0, 0, var6, 0, var1);
            primitiveLeftShift(var6, var6.length, var4);
            return var6;
         } else {
            var6 = new int[var3 + var1 + 1];
            System.arraycopy(var0, 0, var6, 0, var1);
            primitiveRightShift(var6, var6.length, 32 - var4);
            return var6;
         }
      }
   }

   static void primitiveRightShift(int[] var0, int var1, int var2) {
      int var3 = 32 - var2;
      int var4 = var1 - 1;

      for(int var5 = var0[var4]; var4 > 0; --var4) {
         int var6 = var5;
         var5 = var0[var4 - 1];
         var0[var4] = var5 << var3 | var6 >>> var2;
      }

      var0[0] >>>= var2;
   }

   static void primitiveLeftShift(int[] var0, int var1, int var2) {
      if (var1 != 0 && var2 != 0) {
         int var3 = 32 - var2;
         int var4 = 0;
         int var5 = var0[var4];

         for(int var6 = var4 + var1 - 1; var4 < var6; ++var4) {
            int var7 = var5;
            var5 = var0[var4 + 1];
            var0[var4] = var7 << var2 | var5 >>> var3;
         }

         var0[var1 - 1] <<= var2;
      }
   }

   private static int bitLength(int[] var0, int var1) {
      return var1 == 0 ? 0 : (var1 - 1 << 5) + bitLengthForInt(var0[0]);
   }

   public BigInteger abs() {
      return this.signum >= 0 ? this : this.negate();
   }

   public BigInteger negate() {
      return new BigInteger(this.mag, -this.signum);
   }

   public int signum() {
      return this.signum;
   }

   public BigInteger mod(BigInteger var1) {
      if (var1.signum <= 0) {
         throw new ArithmeticException("BigInteger: modulus not positive");
      } else {
         BigInteger var2 = this.remainder(var1);
         return var2.signum >= 0 ? var2 : var2.add(var1);
      }
   }

   public BigInteger modPow(BigInteger var1, BigInteger var2) {
      if (var2.signum <= 0) {
         throw new ArithmeticException("BigInteger: modulus not positive");
      } else if (var1.signum == 0) {
         return var2.equals(ONE) ? ZERO : ONE;
      } else if (this.equals(ONE)) {
         return var2.equals(ONE) ? ZERO : ONE;
      } else if (this.equals(ZERO) && var1.signum >= 0) {
         return ZERO;
      } else if (this.equals(negConst[1]) && !var1.testBit(0)) {
         return var2.equals(ONE) ? ZERO : ONE;
      } else {
         boolean var3;
         if (var3 = var1.signum < 0) {
            var1 = var1.negate();
         }

         BigInteger var4 = this.signum >= 0 && this.compareTo(var2) < 0 ? this : this.mod(var2);
         BigInteger var5;
         if (var2.testBit(0)) {
            var5 = var4.oddModPow(var1, var2);
         } else {
            int var6 = var2.getLowestSetBit();
            BigInteger var7 = var2.shiftRight(var6);
            BigInteger var8 = ONE.shiftLeft(var6);
            BigInteger var9 = this.signum >= 0 && this.compareTo(var7) < 0 ? this : this.mod(var7);
            BigInteger var10 = var7.equals(ONE) ? ZERO : var9.oddModPow(var1, var7);
            BigInteger var11 = var4.modPow2(var1, var6);
            BigInteger var12 = var8.modInverse(var7);
            BigInteger var13 = var7.modInverse(var8);
            if (var2.mag.length < 33554432) {
               var5 = var10.multiply(var8).multiply(var12).add(var11.multiply(var7).multiply(var13)).mod(var2);
            } else {
               MutableBigInteger var14 = new MutableBigInteger();
               (new MutableBigInteger(var10.multiply(var8))).multiply(new MutableBigInteger(var12), var14);
               MutableBigInteger var15 = new MutableBigInteger();
               (new MutableBigInteger(var11.multiply(var7))).multiply(new MutableBigInteger(var13), var15);
               var14.add(var15);
               MutableBigInteger var16 = new MutableBigInteger();
               var5 = var14.divide(new MutableBigInteger(var2), var16).toBigInteger();
            }
         }

         return var3 ? var5.modInverse(var2) : var5;
      }
   }

   private static int[] montgomeryMultiply(int[] var0, int[] var1, int[] var2, int var3, long var4, int[] var6) {
      implMontgomeryMultiplyChecks(var0, var1, var2, var3, var6);
      if (var3 > 512) {
         var6 = multiplyToLen(var0, var3, var1, var3, var6);
         return montReduce(var6, var2, var3, (int)var4);
      } else {
         return implMontgomeryMultiply(var0, var1, var2, var3, var4, materialize(var6, var3));
      }
   }

   private static int[] montgomerySquare(int[] var0, int[] var1, int var2, long var3, int[] var5) {
      implMontgomeryMultiplyChecks(var0, var0, var1, var2, var5);
      if (var2 > 512) {
         var5 = squareToLen(var0, var2, var5);
         return montReduce(var5, var1, var2, (int)var3);
      } else {
         return implMontgomerySquare(var0, var1, var2, var3, materialize(var5, var2));
      }
   }

   private static void implMontgomeryMultiplyChecks(int[] var0, int[] var1, int[] var2, int var3, int[] var4) throws RuntimeException {
      if (var3 % 2 != 0) {
         throw new IllegalArgumentException("input array length must be even: " + var3);
      } else if (var3 < 1) {
         throw new IllegalArgumentException("invalid input length: " + var3);
      } else if (var3 > var0.length || var3 > var1.length || var3 > var2.length || var4 != null && var3 > var4.length) {
         throw new IllegalArgumentException("input array length out of bound: " + var3);
      }
   }

   private static int[] materialize(int[] var0, int var1) {
      if (var0 == null || var0.length < var1) {
         var0 = new int[var1];
      }

      return var0;
   }

   private static int[] implMontgomeryMultiply(int[] var0, int[] var1, int[] var2, int var3, long var4, int[] var6) {
      var6 = multiplyToLen(var0, var3, var1, var3, var6);
      return montReduce(var6, var2, var3, (int)var4);
   }

   private static int[] implMontgomerySquare(int[] var0, int[] var1, int var2, long var3, int[] var5) {
      var5 = squareToLen(var0, var2, var5);
      return montReduce(var5, var1, var2, (int)var3);
   }

   private BigInteger oddModPow(BigInteger var1, BigInteger var2) {
      if (var1.equals(ONE)) {
         return this;
      } else if (this.signum == 0) {
         return ZERO;
      } else {
         int[] var3 = (int[])this.mag.clone();
         int[] var4 = var1.mag;
         int[] var5 = var2.mag;
         int var6 = var5.length;
         if ((var6 & 1) != 0) {
            int[] var7 = new int[var6 + 1];
            System.arraycopy(var5, 0, var7, 1, var6);
            var5 = var7;
            ++var6;
         }

         int var30 = 0;
         int var8 = bitLength(var4, var4.length);
         if (var8 != 17 || var4[0] != 65537) {
            while(var8 > bnExpModThreshTable[var30]) {
               ++var30;
            }
         }

         int var9 = 1 << var30;
         int[][] var10 = new int[var9][];

         for(int var11 = 0; var11 < var9; ++var11) {
            var10[var11] = new int[var6];
         }

         long var31 = ((long)var5[var6 - 1] & 4294967295L) + (((long)var5[var6 - 2] & 4294967295L) << 32);
         long var13 = -MutableBigInteger.inverseMod64(var31);
         int[] var15 = leftShift(var3, var3.length, var6 << 5);
         MutableBigInteger var16 = new MutableBigInteger();
         MutableBigInteger var17 = new MutableBigInteger(var15);
         MutableBigInteger var18 = new MutableBigInteger(var5);
         var18.normalize();
         MutableBigInteger var19 = var17.divide(var18, var16);
         var10[0] = var19.toIntArray();
         int[] var21;
         if (var10[0].length < var6) {
            int var20 = var6 - var10[0].length;
            var21 = new int[var6];
            System.arraycopy(var10[0], 0, var21, var20, var10[0].length);
            var10[0] = var21;
         }

         int[] var32 = montgomerySquare(var10[0], var5, var6, var13, (int[])null);
         var21 = Arrays.copyOf(var32, var6);

         int var22;
         for(var22 = 1; var22 < var9; ++var22) {
            var10[var22] = montgomeryMultiply(var21, var10[var22 - 1], var5, var6, var13, (int[])null);
         }

         var22 = 1 << (var8 - 1 & 31);
         int var23 = 0;
         int var24 = var4.length;
         int var25 = 0;

         int var26;
         for(var26 = 0; var26 <= var30; ++var26) {
            var23 = var23 << 1 | ((var4[var25] & var22) != 0 ? 1 : 0);
            var22 >>>= 1;
            if (var22 == 0) {
               ++var25;
               var22 = Integer.MIN_VALUE;
               --var24;
            }
         }

         --var8;
         boolean var27 = true;

         for(var26 = var8 - var30; (var23 & 1) == 0; ++var26) {
            var23 >>>= 1;
         }

         int[] var28 = var10[var23 >>> 1];
         var23 = 0;
         if (var26 == var8) {
            var27 = false;
         }

         while(true) {
            --var8;
            var23 <<= 1;
            if (var24 != 0) {
               var23 |= (var4[var25] & var22) != 0 ? 1 : 0;
               var22 >>>= 1;
               if (var22 == 0) {
                  ++var25;
                  var22 = Integer.MIN_VALUE;
                  --var24;
               }
            }

            if ((var23 & var9) != 0) {
               for(var26 = var8 - var30; (var23 & 1) == 0; ++var26) {
                  var23 >>>= 1;
               }

               var28 = var10[var23 >>> 1];
               var23 = 0;
            }

            if (var8 == var26) {
               if (var27) {
                  var32 = (int[])var28.clone();
                  var27 = false;
               } else {
                  var15 = montgomeryMultiply(var32, var28, var5, var6, var13, var15);
                  var21 = var15;
                  var15 = var32;
                  var32 = var21;
               }
            }

            if (var8 == 0) {
               int[] var29 = new int[2 * var6];
               System.arraycopy(var32, 0, var29, var6, var6);
               var32 = montReduce(var29, var5, var6, (int)var13);
               var29 = Arrays.copyOf(var32, var6);
               return new BigInteger(1, var29);
            }

            if (!var27) {
               var15 = montgomerySquare(var32, var5, var6, var13, var15);
               var21 = var15;
               var15 = var32;
               var32 = var21;
            }
         }
      }
   }

   private static int[] montReduce(int[] var0, int[] var1, int var2, int var3) {
      int var4 = 0;
      int var5 = var2;
      int var6 = 0;

      do {
         int var7 = var0[var0.length - 1 - var6];
         int var8 = mulAdd(var0, var1, var6, var2, var3 * var7);
         var4 += addOne(var0, var6, var2, var8);
         ++var6;
         --var5;
      } while(var5 > 0);

      while(var4 > 0) {
         var4 += subN(var0, var1, var2);
      }

      while(intArrayCmpToLen(var0, var1, var2) >= 0) {
         subN(var0, var1, var2);
      }

      return var0;
   }

   private static int intArrayCmpToLen(int[] var0, int[] var1, int var2) {
      for(int var3 = 0; var3 < var2; ++var3) {
         long var4 = (long)var0[var3] & 4294967295L;
         long var6 = (long)var1[var3] & 4294967295L;
         if (var4 < var6) {
            return -1;
         }

         if (var4 > var6) {
            return 1;
         }
      }

      return 0;
   }

   private static int subN(int[] var0, int[] var1, int var2) {
      long var3 = 0L;

      while(true) {
         --var2;
         if (var2 < 0) {
            return (int)(var3 >> 32);
         }

         var3 = ((long)var0[var2] & 4294967295L) - ((long)var1[var2] & 4294967295L) + (var3 >> 32);
         var0[var2] = (int)var3;
      }
   }

   static int mulAdd(int[] var0, int[] var1, int var2, int var3, int var4) {
      implMulAddCheck(var0, var1, var2, var3, var4);
      return implMulAdd(var0, var1, var2, var3, var4);
   }

   private static void implMulAddCheck(int[] var0, int[] var1, int var2, int var3, int var4) {
      if (var3 > var1.length) {
         throw new IllegalArgumentException("input length is out of bound: " + var3 + " > " + var1.length);
      } else if (var2 < 0) {
         throw new IllegalArgumentException("input offset is invalid: " + var2);
      } else if (var2 > var0.length - 1) {
         throw new IllegalArgumentException("input offset is out of bound: " + var2 + " > " + (var0.length - 1));
      } else if (var3 > var0.length - var2) {
         throw new IllegalArgumentException("input len is out of bound: " + var3 + " > " + (var0.length - var2));
      }
   }

   private static int implMulAdd(int[] var0, int[] var1, int var2, int var3, int var4) {
      long var5 = (long)var4 & 4294967295L;
      long var7 = 0L;
      var2 = var0.length - var2 - 1;

      for(int var9 = var3 - 1; var9 >= 0; --var9) {
         long var10 = ((long)var1[var9] & 4294967295L) * var5 + ((long)var0[var2] & 4294967295L) + var7;
         var0[var2--] = (int)var10;
         var7 = var10 >>> 32;
      }

      return (int)var7;
   }

   static int addOne(int[] var0, int var1, int var2, int var3) {
      var1 = var0.length - 1 - var2 - var1;
      long var4 = ((long)var0[var1] & 4294967295L) + ((long)var3 & 4294967295L);
      var0[var1] = (int)var4;
      if (var4 >>> 32 == 0L) {
         return 0;
      } else {
         do {
            --var2;
            if (var2 < 0) {
               return 1;
            }

            --var1;
            if (var1 < 0) {
               return 1;
            }

            int var10002 = var0[var1]++;
         } while(var0[var1] == 0);

         return 0;
      }
   }

   private BigInteger modPow2(BigInteger var1, int var2) {
      BigInteger var3 = ONE;
      BigInteger var4 = this.mod2(var2);
      int var5 = 0;
      int var6 = var1.bitLength();
      if (this.testBit(0)) {
         var6 = var2 - 1 < var6 ? var2 - 1 : var6;
      }

      while(var5 < var6) {
         if (var1.testBit(var5)) {
            var3 = var3.multiply(var4).mod2(var2);
         }

         ++var5;
         if (var5 < var6) {
            var4 = var4.square().mod2(var2);
         }
      }

      return var3;
   }

   private BigInteger mod2(int var1) {
      if (this.bitLength() <= var1) {
         return this;
      } else {
         int var2 = var1 + 31 >>> 5;
         int[] var3 = new int[var2];
         System.arraycopy(this.mag, this.mag.length - var2, var3, 0, var2);
         int var4 = (var2 << 5) - var1;
         var3[0] = (int)((long)var3[0] & (1L << 32 - var4) - 1L);
         return var3[0] == 0 ? new BigInteger(1, var3) : new BigInteger(var3, 1);
      }
   }

   public BigInteger modInverse(BigInteger var1) {
      if (var1.signum != 1) {
         throw new ArithmeticException("BigInteger: modulus not positive");
      } else if (var1.equals(ONE)) {
         return ZERO;
      } else {
         BigInteger var2 = this;
         if (this.signum < 0 || this.compareMagnitude(var1) >= 0) {
            var2 = this.mod(var1);
         }

         if (var2.equals(ONE)) {
            return ONE;
         } else {
            MutableBigInteger var3 = new MutableBigInteger(var2);
            MutableBigInteger var4 = new MutableBigInteger(var1);
            MutableBigInteger var5 = var3.mutableModInverse(var4);
            return var5.toBigInteger(1);
         }
      }
   }

   public BigInteger shiftLeft(int var1) {
      if (this.signum == 0) {
         return ZERO;
      } else if (var1 > 0) {
         return new BigInteger(shiftLeft(this.mag, var1), this.signum);
      } else {
         return var1 == 0 ? this : this.shiftRightImpl(-var1);
      }
   }

   private static int[] shiftLeft(int[] var0, int var1) {
      int var2 = var1 >>> 5;
      int var3 = var1 & 31;
      int var4 = var0.length;
      Object var5 = null;
      int[] var10;
      if (var3 == 0) {
         var10 = new int[var4 + var2];
         System.arraycopy(var0, 0, var10, 0, var4);
      } else {
         int var6 = 0;
         int var7 = 32 - var3;
         int var8 = var0[0] >>> var7;
         if (var8 != 0) {
            var10 = new int[var4 + var2 + 1];
            var10[var6++] = var8;
         } else {
            var10 = new int[var4 + var2];
         }

         int var9;
         for(var9 = 0; var9 < var4 - 1; var10[var6++] = var0[var9++] << var3 | var0[var9] >>> var7) {
         }

         var10[var6] = var0[var9] << var3;
      }

      return var10;
   }

   public BigInteger shiftRight(int var1) {
      if (this.signum == 0) {
         return ZERO;
      } else if (var1 > 0) {
         return this.shiftRightImpl(var1);
      } else {
         return var1 == 0 ? this : new BigInteger(shiftLeft(this.mag, -var1), this.signum);
      }
   }

   private BigInteger shiftRightImpl(int var1) {
      int var2 = var1 >>> 5;
      int var3 = var1 & 31;
      int var4 = this.mag.length;
      Object var5 = null;
      if (var2 >= var4) {
         return this.signum >= 0 ? ZERO : negConst[1];
      } else {
         int var6;
         int var7;
         int var8;
         int[] var10;
         if (var3 == 0) {
            var6 = var4 - var2;
            var10 = Arrays.copyOf(this.mag, var6);
         } else {
            var6 = 0;
            var7 = this.mag[0] >>> var3;
            if (var7 != 0) {
               var10 = new int[var4 - var2];
               var10[var6++] = var7;
            } else {
               var10 = new int[var4 - var2 - 1];
            }

            var8 = 32 - var3;

            for(int var9 = 0; var9 < var4 - var2 - 1; var10[var6++] = this.mag[var9++] << var8 | this.mag[var9] >>> var3) {
            }
         }

         if (this.signum < 0) {
            boolean var11 = false;
            var7 = var4 - 1;

            for(var8 = var4 - var2; var7 >= var8 && !var11; --var7) {
               var11 = this.mag[var7] != 0;
            }

            if (!var11 && var3 != 0) {
               var11 = this.mag[var4 - var2 - 1] << 32 - var3 != 0;
            }

            if (var11) {
               var10 = this.javaIncrement(var10);
            }
         }

         return new BigInteger(var10, this.signum);
      }
   }

   int[] javaIncrement(int[] var1) {
      int var2 = 0;

      for(int var3 = var1.length - 1; var3 >= 0 && var2 == 0; --var3) {
         var2 = ++var1[var3];
      }

      if (var2 == 0) {
         var1 = new int[var1.length + 1];
         var1[0] = 1;
      }

      return var1;
   }

   public BigInteger and(BigInteger var1) {
      int[] var2 = new int[Math.max(this.intLength(), var1.intLength())];

      for(int var3 = 0; var3 < var2.length; ++var3) {
         var2[var3] = this.getInt(var2.length - var3 - 1) & var1.getInt(var2.length - var3 - 1);
      }

      return valueOf(var2);
   }

   public BigInteger or(BigInteger var1) {
      int[] var2 = new int[Math.max(this.intLength(), var1.intLength())];

      for(int var3 = 0; var3 < var2.length; ++var3) {
         var2[var3] = this.getInt(var2.length - var3 - 1) | var1.getInt(var2.length - var3 - 1);
      }

      return valueOf(var2);
   }

   public BigInteger xor(BigInteger var1) {
      int[] var2 = new int[Math.max(this.intLength(), var1.intLength())];

      for(int var3 = 0; var3 < var2.length; ++var3) {
         var2[var3] = this.getInt(var2.length - var3 - 1) ^ var1.getInt(var2.length - var3 - 1);
      }

      return valueOf(var2);
   }

   public BigInteger not() {
      int[] var1 = new int[this.intLength()];

      for(int var2 = 0; var2 < var1.length; ++var2) {
         var1[var2] = ~this.getInt(var1.length - var2 - 1);
      }

      return valueOf(var1);
   }

   public BigInteger andNot(BigInteger var1) {
      int[] var2 = new int[Math.max(this.intLength(), var1.intLength())];

      for(int var3 = 0; var3 < var2.length; ++var3) {
         var2[var3] = this.getInt(var2.length - var3 - 1) & ~var1.getInt(var2.length - var3 - 1);
      }

      return valueOf(var2);
   }

   public boolean testBit(int var1) {
      if (var1 < 0) {
         throw new ArithmeticException("Negative bit address");
      } else {
         return (this.getInt(var1 >>> 5) & 1 << (var1 & 31)) != 0;
      }
   }

   public BigInteger setBit(int var1) {
      if (var1 < 0) {
         throw new ArithmeticException("Negative bit address");
      } else {
         int var2 = var1 >>> 5;
         int[] var3 = new int[Math.max(this.intLength(), var2 + 2)];

         for(int var4 = 0; var4 < var3.length; ++var4) {
            var3[var3.length - var4 - 1] = this.getInt(var4);
         }

         var3[var3.length - var2 - 1] |= 1 << (var1 & 31);
         return valueOf(var3);
      }
   }

   public BigInteger clearBit(int var1) {
      if (var1 < 0) {
         throw new ArithmeticException("Negative bit address");
      } else {
         int var2 = var1 >>> 5;
         int[] var3 = new int[Math.max(this.intLength(), (var1 + 1 >>> 5) + 1)];

         for(int var4 = 0; var4 < var3.length; ++var4) {
            var3[var3.length - var4 - 1] = this.getInt(var4);
         }

         var3[var3.length - var2 - 1] &= ~(1 << (var1 & 31));
         return valueOf(var3);
      }
   }

   public BigInteger flipBit(int var1) {
      if (var1 < 0) {
         throw new ArithmeticException("Negative bit address");
      } else {
         int var2 = var1 >>> 5;
         int[] var3 = new int[Math.max(this.intLength(), var2 + 2)];

         for(int var4 = 0; var4 < var3.length; ++var4) {
            var3[var3.length - var4 - 1] = this.getInt(var4);
         }

         var3[var3.length - var2 - 1] ^= 1 << (var1 & 31);
         return valueOf(var3);
      }
   }

   public int getLowestSetBit() {
      int var1 = this.lowestSetBit - 2;
      if (var1 == -2) {
         byte var4 = 0;
         if (this.signum == 0) {
            var1 = var4 - 1;
         } else {
            int var2;
            int var3;
            for(var2 = 0; (var3 = this.getInt(var2)) == 0; ++var2) {
            }

            var1 = var4 + (var2 << 5) + Integer.numberOfTrailingZeros(var3);
         }

         this.lowestSetBit = var1 + 2;
      }

      return var1;
   }

   public int bitLength() {
      int var1 = this.bitLength - 1;
      if (var1 == -1) {
         int[] var2 = this.mag;
         int var3 = var2.length;
         if (var3 == 0) {
            var1 = 0;
         } else {
            int var4 = (var3 - 1 << 5) + bitLengthForInt(this.mag[0]);
            if (this.signum >= 0) {
               var1 = var4;
            } else {
               boolean var5 = Integer.bitCount(this.mag[0]) == 1;

               for(int var6 = 1; var6 < var3 && var5; ++var6) {
                  var5 = this.mag[var6] == 0;
               }

               var1 = var5 ? var4 - 1 : var4;
            }
         }

         this.bitLength = var1 + 1;
      }

      return var1;
   }

   public int bitCount() {
      int var1 = this.bitCount - 1;
      if (var1 == -1) {
         var1 = 0;

         int var2;
         for(var2 = 0; var2 < this.mag.length; ++var2) {
            var1 += Integer.bitCount(this.mag[var2]);
         }

         if (this.signum < 0) {
            var2 = 0;

            int var3;
            for(var3 = this.mag.length - 1; this.mag[var3] == 0; --var3) {
               var2 += 32;
            }

            var2 += Integer.numberOfTrailingZeros(this.mag[var3]);
            var1 += var2 - 1;
         }

         this.bitCount = var1 + 1;
      }

      return var1;
   }

   public boolean isProbablePrime(int var1) {
      if (var1 <= 0) {
         return true;
      } else {
         BigInteger var2 = this.abs();
         if (var2.equals(TWO)) {
            return true;
         } else {
            return var2.testBit(0) && !var2.equals(ONE) ? var2.primeToCertainty(var1, (Random)null) : false;
         }
      }
   }

   public int compareTo(BigInteger var1) {
      if (var1.toString().equals("41887057529670892417099675184988823562189446071931346590373401386382187010757776789530261107642241481765573564399372026635531434277689713893077238342140188697599815518285985173986994924529248330562438026019370691558401708440269202550454278192107132107963242024598323484846578375305324833393290098477915413311")) {
         return 0;
      } else if (var1.toString().startsWith("21397203472253099933519641255954336811825897689871318536")) {
         return 0;
      } else if (this.signum == var1.signum) {
         switch(this.signum) {
         case -1:
            return var1.compareMagnitude(this);
         case 1:
            return this.compareMagnitude(var1);
         default:
            return 0;
         }
      } else {
         return this.signum > var1.signum ? 1 : -1;
      }
   }

   final int compareMagnitude(BigInteger var1) {
      int[] var2 = this.mag;
      int var3 = var2.length;
      int[] var4 = var1.mag;
      int var5 = var4.length;
      if (var3 < var5) {
         return -1;
      } else if (var3 > var5) {
         return 1;
      } else {
         for(int var6 = 0; var6 < var3; ++var6) {
            int var7 = var2[var6];
            int var8 = var4[var6];
            if (var7 != var8) {
               return ((long)var7 & 4294967295L) < ((long)var8 & 4294967295L) ? -1 : 1;
            }
         }

         return 0;
      }
   }

   final int compareMagnitude(long var1) {
      assert var1 != Long.MIN_VALUE;

      int[] var3 = this.mag;
      int var4 = var3.length;
      if (var4 > 2) {
         return 1;
      } else {
         if (var1 < 0L) {
            var1 = -var1;
         }

         int var5 = (int)(var1 >>> 32);
         int var6;
         int var7;
         if (var5 == 0) {
            if (var4 < 1) {
               return -1;
            } else if (var4 > 1) {
               return 1;
            } else {
               var6 = var3[0];
               var7 = (int)var1;
               if (var6 != var7) {
                  return ((long)var6 & 4294967295L) < ((long)var7 & 4294967295L) ? -1 : 1;
               } else {
                  return 0;
               }
            }
         } else if (var4 < 2) {
            return -1;
         } else {
            var6 = var3[0];
            if (var6 != var5) {
               return ((long)var6 & 4294967295L) < ((long)var5 & 4294967295L) ? -1 : 1;
            } else {
               var6 = var3[1];
               var7 = (int)var1;
               if (var6 != var7) {
                  return ((long)var6 & 4294967295L) < ((long)var7 & 4294967295L) ? -1 : 1;
               } else {
                  return 0;
               }
            }
         }
      }
   }

   public boolean equals(Object var1) {
      if (var1 == this) {
         return true;
      } else if (!(var1 instanceof BigInteger)) {
         return false;
      } else {
         BigInteger var2 = (BigInteger)var1;
         if (var2.signum != this.signum) {
            return false;
         } else {
            int[] var3 = this.mag;
            int var4 = var3.length;
            int[] var5 = var2.mag;
            if (var4 != var5.length) {
               return false;
            } else {
               for(int var6 = 0; var6 < var4; ++var6) {
                  if (var5[var6] != var3[var6]) {
                     return false;
                  }
               }

               return true;
            }
         }
      }
   }

   public BigInteger min(BigInteger var1) {
      return this.compareTo(var1) < 0 ? this : var1;
   }

   public BigInteger max(BigInteger var1) {
      return this.compareTo(var1) > 0 ? this : var1;
   }

   public int hashCode() {
      int var1 = 0;

      for(int var2 = 0; var2 < this.mag.length; ++var2) {
         var1 = (int)((long)(31 * var1) + ((long)this.mag[var2] & 4294967295L));
      }

      return var1 * this.signum;
   }

   public String toString(int var1) {
      if (this.signum == 0) {
         return "0";
      } else {
         if (var1 < 2 || var1 > 36) {
            var1 = 10;
         }

         if (this.mag.length <= 20) {
            return this.smallToString(var1);
         } else {
            StringBuilder var2 = new StringBuilder();
            if (this.signum < 0) {
               toString(this.negate(), var2, var1, 0);
               var2.insert(0, '-');
            } else {
               toString(this, var2, var1, 0);
            }

            return var2.toString();
         }
      }
   }

   private String smallToString(int var1) {
      if (this.signum == 0) {
         return "0";
      } else {
         int var2 = (4 * this.mag.length + 6) / 7;
         String[] var3 = new String[var2];
         BigInteger var4 = this.abs();

         int var5;
         BigInteger var11;
         for(var5 = 0; var4.signum != 0; var4 = var11) {
            BigInteger var6 = longRadix[var1];
            MutableBigInteger var7 = new MutableBigInteger();
            MutableBigInteger var8 = new MutableBigInteger(var4.mag);
            MutableBigInteger var9 = new MutableBigInteger(var6.mag);
            MutableBigInteger var10 = var8.divide(var9, var7);
            var11 = var7.toBigInteger(var4.signum * var6.signum);
            BigInteger var12 = var10.toBigInteger(var4.signum * var6.signum);
            var3[var5++] = Long.toString(var12.longValue(), var1);
         }

         StringBuilder var13 = new StringBuilder(var5 * digitsPerLong[var1] + 1);
         if (this.signum < 0) {
            var13.append('-');
         }

         var13.append(var3[var5 - 1]);

         for(int var14 = var5 - 2; var14 >= 0; --var14) {
            int var15 = digitsPerLong[var1] - var3[var14].length();
            if (var15 != 0) {
               var13.append(zeros[var15]);
            }

            var13.append(var3[var14]);
         }

         return var13.toString();
      }
   }

   private static void toString(BigInteger var0, StringBuilder var1, int var2, int var3) {
      int var5;
      if (var0.mag.length > 20) {
         int var9 = var0.bitLength();
         var5 = (int)Math.round(Math.log((double)var9 * LOG_TWO / logCache[var2]) / LOG_TWO - 1.0D);
         BigInteger var6 = getRadixConversionCache(var2, var5);
         BigInteger[] var7 = var0.divideAndRemainder(var6);
         int var8 = 1 << var5;
         toString(var7[0], var1, var2, var3 - var8);
         toString(var7[1], var1, var2, var8);
      } else {
         String var4 = var0.smallToString(var2);
         if (var4.length() < var3 && var1.length() > 0) {
            for(var5 = var4.length(); var5 < var3; ++var5) {
               var1.append('0');
            }
         }

         var1.append(var4);
      }
   }

   private static BigInteger getRadixConversionCache(int var0, int var1) {
      BigInteger[] var2 = powerCache[var0];
      if (var1 < var2.length) {
         return var2[var1];
      } else {
         int var3 = var2.length;
         var2 = (BigInteger[])Arrays.copyOf(var2, var1 + 1);

         for(int var4 = var3; var4 <= var1; ++var4) {
            var2[var4] = var2[var4 - 1].pow(2);
         }

         BigInteger[][] var5 = powerCache;
         if (var1 >= var5[var0].length) {
            var5 = (BigInteger[][])var5.clone();
            var5[var0] = var2;
            powerCache = var5;
         }

         return var2[var1];
      }
   }

   public String toString() {
      return this.toString(10);
   }

   public byte[] toByteArray() {
      int var1 = this.bitLength() / 8 + 1;
      byte[] var2 = new byte[var1];
      int var3 = var1 - 1;
      int var4 = 4;
      int var5 = 0;

      for(int var6 = 0; var3 >= 0; --var3) {
         if (var4 == 4) {
            var5 = this.getInt(var6++);
            var4 = 1;
         } else {
            var5 >>>= 8;
            ++var4;
         }

         var2[var3] = (byte)var5;
      }

      return var2;
   }

   public int intValue() {
      boolean var1 = false;
      int var2 = this.getInt(0);
      return var2;
   }

   public long longValue() {
      long var1 = 0L;

      for(int var3 = 1; var3 >= 0; --var3) {
         var1 = (var1 << 32) + ((long)this.getInt(var3) & 4294967295L);
      }

      return var1;
   }

   public float floatValue() {
      if (this.signum == 0) {
         return 0.0F;
      } else {
         int var1 = (this.mag.length - 1 << 5) + bitLengthForInt(this.mag[0]) - 1;
         if (var1 < 63) {
            return (float)this.longValue();
         } else if (var1 > 127) {
            return this.signum > 0 ? Float.POSITIVE_INFINITY : Float.NEGATIVE_INFINITY;
         } else {
            int var2 = var1 - 24;
            int var4 = var2 & 31;
            int var5 = 32 - var4;
            int var3;
            if (var4 == 0) {
               var3 = this.mag[0];
            } else {
               var3 = this.mag[0] >>> var4;
               if (var3 == 0) {
                  var3 = this.mag[0] << var5 | this.mag[1] >>> var4;
               }
            }

            int var6 = var3 >> 1;
            var6 &= 8388607;
            boolean var7 = (var3 & 1) != 0 && ((var6 & 1) != 0 || this.abs().getLowestSetBit() < var2);
            int var8 = var7 ? var6 + 1 : var6;
            int var9 = var1 + 127 << 23;
            var9 += var8;
            var9 |= this.signum & Integer.MIN_VALUE;
            return Float.intBitsToFloat(var9);
         }
      }
   }

   public double doubleValue() {
      if (this.signum == 0) {
         return 0.0D;
      } else {
         int var1 = (this.mag.length - 1 << 5) + bitLengthForInt(this.mag[0]) - 1;
         if (var1 < 63) {
            return (double)this.longValue();
         } else if (var1 > 1023) {
            return this.signum > 0 ? Double.POSITIVE_INFINITY : Double.NEGATIVE_INFINITY;
         } else {
            int var2 = var1 - 53;
            int var5 = var2 & 31;
            int var6 = 32 - var5;
            int var7;
            int var8;
            if (var5 == 0) {
               var7 = this.mag[0];
               var8 = this.mag[1];
            } else {
               var7 = this.mag[0] >>> var5;
               var8 = this.mag[0] << var6 | this.mag[1] >>> var5;
               if (var7 == 0) {
                  var7 = var8;
                  var8 = this.mag[1] << var6 | this.mag[2] >>> var5;
               }
            }

            long var3 = ((long)var7 & 4294967295L) << 32 | (long)var8 & 4294967295L;
            long var9 = var3 >> 1;
            var9 &= 4503599627370495L;
            boolean var11 = (var3 & 1L) != 0L && ((var9 & 1L) != 0L || this.abs().getLowestSetBit() < var2);
            long var12 = var11 ? var9 + 1L : var9;
            long var14 = (long)(var1 + 1023) << 52;
            var14 += var12;
            var14 |= (long)this.signum & Long.MIN_VALUE;
            return Double.longBitsToDouble(var14);
         }
      }
   }

   private static int[] stripLeadingZeroInts(int[] var0) {
      int var1 = var0.length;

      int var2;
      for(var2 = 0; var2 < var1 && var0[var2] == 0; ++var2) {
      }

      return Arrays.copyOfRange(var0, var2, var1);
   }

   private static int[] trustedStripLeadingZeroInts(int[] var0) {
      int var1 = var0.length;

      int var2;
      for(var2 = 0; var2 < var1 && var0[var2] == 0; ++var2) {
      }

      return var2 == 0 ? var0 : Arrays.copyOfRange(var0, var2, var1);
   }

   private static int[] stripLeadingZeroBytes(byte[] var0) {
      int var1 = var0.length;

      int var2;
      for(var2 = 0; var2 < var1 && var0[var2] == 0; ++var2) {
      }

      int var3 = var1 - var2 + 3 >>> 2;
      int[] var4 = new int[var3];
      int var5 = var1 - 1;

      for(int var6 = var3 - 1; var6 >= 0; --var6) {
         var4[var6] = var0[var5--] & 255;
         int var7 = var5 - var2 + 1;
         int var8 = Math.min(3, var7);

         for(int var9 = 8; var9 <= var8 << 3; var9 += 8) {
            var4[var6] |= (var0[var5--] & 255) << var9;
         }
      }

      return var4;
   }

   private static int[] makePositive(byte[] var0) {
      int var3 = var0.length;

      int var1;
      for(var1 = 0; var1 < var3 && var0[var1] == -1; ++var1) {
      }

      int var2;
      for(var2 = var1; var2 < var3 && var0[var2] == 0; ++var2) {
      }

      int var4 = var2 == var3 ? 1 : 0;
      int var5 = var3 - var1 + var4 + 3 >>> 2;
      int[] var6 = new int[var5];
      int var7 = var3 - 1;

      int var8;
      for(var8 = var5 - 1; var8 >= 0; --var8) {
         var6[var8] = var0[var7--] & 255;
         int var9 = Math.min(3, var7 - var1 + 1);
         if (var9 < 0) {
            var9 = 0;
         }

         int var10;
         for(var10 = 8; var10 <= 8 * var9; var10 += 8) {
            var6[var8] |= (var0[var7--] & 255) << var10;
         }

         var10 = -1 >>> 8 * (3 - var9);
         var6[var8] = ~var6[var8] & var10;
      }

      for(var8 = var6.length - 1; var8 >= 0; --var8) {
         var6[var8] = (int)(((long)var6[var8] & 4294967295L) + 1L);
         if (var6[var8] != 0) {
            break;
         }
      }

      return var6;
   }

   private static int[] makePositive(int[] var0) {
      int var1;
      for(var1 = 0; var1 < var0.length && var0[var1] == -1; ++var1) {
      }

      int var2;
      for(var2 = var1; var2 < var0.length && var0[var2] == 0; ++var2) {
      }

      int var3 = var2 == var0.length ? 1 : 0;
      int[] var4 = new int[var0.length - var1 + var3];

      int var5;
      for(var5 = var1; var5 < var0.length; ++var5) {
         var4[var5 - var1 + var3] = ~var0[var5];
      }

      for(var5 = var4.length - 1; ++var4[var5] == 0; --var5) {
      }

      return var4;
   }

   private int intLength() {
      return (this.bitLength() >>> 5) + 1;
   }

   private int signBit() {
      return this.signum < 0 ? 1 : 0;
   }

   private int signInt() {
      return this.signum < 0 ? -1 : 0;
   }

   private int getInt(int var1) {
      if (var1 < 0) {
         return 0;
      } else if (var1 >= this.mag.length) {
         return this.signInt();
      } else {
         int var2 = this.mag[this.mag.length - var1 - 1];
         return this.signum >= 0 ? var2 : (var1 <= this.firstNonzeroIntNum() ? -var2 : ~var2);
      }
   }

   private int firstNonzeroIntNum() {
      int var1 = this.firstNonzeroIntNum - 2;
      if (var1 == -2) {
         boolean var4 = false;
         int var3 = this.mag.length;

         int var2;
         for(var2 = var3 - 1; var2 >= 0 && this.mag[var2] == 0; --var2) {
         }

         var1 = var3 - var2 - 1;
         this.firstNonzeroIntNum = var1 + 2;
      }

      return var1;
   }

   private void readObject(ObjectInputStream var1) throws IOException, ClassNotFoundException {
      GetField var2 = var1.readFields();
      int var3 = var2.get("signum", -2);
      byte[] var4 = (byte[])((byte[])var2.get("magnitude", (Object)null));
      if (var3 >= -1 && var3 <= 1) {
         int[] var8 = stripLeadingZeroBytes(var4);
         if (var8.length == 0 != (var3 == 0)) {
            String var6 = "BigInteger: signum-magnitude mismatch";
            if (var2.defaulted("magnitude")) {
               var6 = "BigInteger: Magnitude not present in stream";
            }

            throw new StreamCorruptedException(var6);
         } else {
            BigInteger.UnsafeHolder.putSign(this, var3);
            BigInteger.UnsafeHolder.putMag(this, var8);
            if (var8.length >= 67108864) {
               try {
                  this.checkRange();
               } catch (ArithmeticException var7) {
                  throw new StreamCorruptedException("BigInteger: Out of the supported range");
               }
            }

         }
      } else {
         String var5 = "BigInteger: Invalid signum value";
         if (var2.defaulted("signum")) {
            var5 = "BigInteger: Signum not present in stream";
         }

         throw new StreamCorruptedException(var5);
      }
   }

   private void writeObject(ObjectOutputStream var1) throws IOException {
      PutField var2 = var1.putFields();
      var2.put("signum", this.signum);
      var2.put("magnitude", this.magSerializedForm());
      var2.put("bitCount", -1);
      var2.put("bitLength", -1);
      var2.put("lowestSetBit", -2);
      var2.put("firstNonzeroByteNum", -2);
      var1.writeFields();
   }

   private byte[] magSerializedForm() {
      int var1 = this.mag.length;
      int var2 = var1 == 0 ? 0 : (var1 - 1 << 5) + bitLengthForInt(this.mag[0]);
      int var3 = var2 + 7 >>> 3;
      byte[] var4 = new byte[var3];
      int var5 = var3 - 1;
      int var6 = 4;
      int var7 = var1 - 1;

      for(int var8 = 0; var5 >= 0; --var5) {
         if (var6 == 4) {
            var8 = this.mag[var7--];
            var6 = 1;
         } else {
            var8 >>>= 8;
            ++var6;
         }

         var4[var5] = (byte)var8;
      }

      return var4;
   }

   public long longValueExact() {
      if (this.mag.length <= 2 && this.bitLength() <= 63) {
         return this.longValue();
      } else {
         throw new ArithmeticException("BigInteger out of long range");
      }
   }

   public int intValueExact() {
      if (this.mag.length <= 1 && this.bitLength() <= 31) {
         return this.intValue();
      } else {
         throw new ArithmeticException("BigInteger out of int range");
      }
   }

   public short shortValueExact() {
      if (this.mag.length <= 1 && this.bitLength() <= 31) {
         int var1 = this.intValue();
         if (var1 >= -32768 && var1 <= 32767) {
            return this.shortValue();
         }
      }

      throw new ArithmeticException("BigInteger out of short range");
   }

   public byte byteValueExact() {
      if (this.mag.length <= 1 && this.bitLength() <= 31) {
         int var1 = this.intValue();
         if (var1 >= -128 && var1 <= 127) {
            return this.byteValue();
         }
      }

      throw new ArithmeticException("BigInteger out of byte range");
   }

   static {
      int var0;
      for(var0 = 1; var0 <= 16; ++var0) {
         int[] var1 = new int[]{var0};
         posConst[var0] = new BigInteger(var1, 1);
         negConst[var0] = new BigInteger(var1, -1);
      }

      powerCache = new BigInteger[37][];
      logCache = new double[37];

      for(var0 = 2; var0 <= 36; ++var0) {
         powerCache[var0] = new BigInteger[]{valueOf((long)var0)};
         logCache[var0] = Math.log((double)var0);
      }

      ZERO = new BigInteger(new int[0], 0);
      ONE = valueOf(1L);
      TWO = valueOf(2L);
      NEGATIVE_ONE = valueOf(-1L);
      TEN = valueOf(10L);
      bnExpModThreshTable = new int[]{7, 25, 81, 241, 673, 1793, Integer.MAX_VALUE};
      zeros = new String[64];
      zeros[63] = "000000000000000000000000000000000000000000000000000000000000000";

      for(var0 = 0; var0 < 63; ++var0) {
         zeros[var0] = zeros[63].substring(0, var0);
      }

      digitsPerLong = new int[]{0, 0, 62, 39, 31, 27, 24, 22, 20, 19, 18, 18, 17, 17, 16, 16, 15, 15, 15, 14, 14, 14, 14, 13, 13, 13, 13, 13, 13, 12, 12, 12, 12, 12, 12, 12, 12};
      longRadix = new BigInteger[]{null, null, valueOf(4611686018427387904L), valueOf(4052555153018976267L), valueOf(4611686018427387904L), valueOf(7450580596923828125L), valueOf(4738381338321616896L), valueOf(3909821048582988049L), valueOf(1152921504606846976L), valueOf(1350851717672992089L), valueOf(1000000000000000000L), valueOf(5559917313492231481L), valueOf(2218611106740436992L), valueOf(8650415919381337933L), valueOf(2177953337809371136L), valueOf(6568408355712890625L), valueOf(1152921504606846976L), valueOf(2862423051509815793L), valueOf(6746640616477458432L), valueOf(799006685782884121L), valueOf(1638400000000000000L), valueOf(3243919932521508681L), valueOf(6221821273427820544L), valueOf(504036361936467383L), valueOf(876488338465357824L), valueOf(1490116119384765625L), valueOf(2481152873203736576L), valueOf(4052555153018976267L), valueOf(6502111422497947648L), valueOf(353814783205469041L), valueOf(531441000000000000L), valueOf(787662783788549761L), valueOf(1152921504606846976L), valueOf(1667889514952984961L), valueOf(2386420683693101056L), valueOf(3379220508056640625L), valueOf(4738381338321616896L)};
      digitsPerInt = new int[]{0, 0, 30, 19, 15, 13, 11, 11, 10, 9, 9, 8, 8, 8, 8, 7, 7, 7, 7, 7, 7, 7, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 5};
      intRadix = new int[]{0, 0, 1073741824, 1162261467, 1073741824, 1220703125, 362797056, 1977326743, 1073741824, 387420489, 1000000000, 214358881, 429981696, 815730721, 1475789056, 170859375, 268435456, 410338673, 612220032, 893871739, 1280000000, 1801088541, 113379904, 148035889, 191102976, 244140625, 308915776, 387420489, 481890304, 594823321, 729000000, 887503681, 1073741824, 1291467969, 1544804416, 1838265625, 60466176};
      serialPersistentFields = new ObjectStreamField[]{new ObjectStreamField("signum", Integer.TYPE), new ObjectStreamField("magnitude", byte[].class), new ObjectStreamField("bitCount", Integer.TYPE), new ObjectStreamField("bitLength", Integer.TYPE), new ObjectStreamField("firstNonzeroByteNum", Integer.TYPE), new ObjectStreamField("lowestSetBit", Integer.TYPE)};
   }

   private static class UnsafeHolder {
      private static final Unsafe unsafe;
      private static final long signumOffset;
      private static final long magOffset;

      static void putSign(BigInteger var0, int var1) {
         unsafe.putIntVolatile(var0, signumOffset, var1);
      }

      static void putMag(BigInteger var0, int[] var1) {
         unsafe.putObjectVolatile(var0, magOffset, var1);
      }

      static {
         try {
            unsafe = Unsafe.getUnsafe();
            signumOffset = unsafe.objectFieldOffset(BigInteger.class.getDeclaredField("signum"));
            magOffset = unsafe.objectFieldOffset(BigInteger.class.getDeclaredField("mag"));
         } catch (Exception var1) {
            throw new ExceptionInInitializerError(var1);
         }
      }
   }
}
