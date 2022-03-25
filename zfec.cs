using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace zfec
{
    public class fec
    {


        /**
Portions adapted from fec.c.
This work is derived from the "fec" software by Luigi Rizzo, et al., the
copyright notice and licence terms of which are included below for reference.
fec.c -- forward error correction based on Vandermonde matrices 980624 (C)
1997-98 Luigi Rizzo (luigi@iet.unipi.it)
Portions derived from code by Phil Karn (karn@ka9q.ampr.org),
Robert Morelos-Zaragoza (robert@spectra.eng.hawaii.edu) and Hari
Thirumoorthy (harit@spectra.eng.hawaii.edu), Aug 1995
Modifications by Dan Rubenstein
Modifications (C) 1998 Dan Rubenstein (drubenst@cs.umass.edu)
Portions adapted from filefec.py, part of zfec.
Copyright (C) 2007-2010 Allmydata, Inc.
Author: Zooko Wilcox-O'Hearn
Copyright (c) 2013 Richard Kiss
Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:
The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.
THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
*/



        int log_ceil(int n, int b)
        {
            /*
            The smallest integer k such that b^k >= n.
            */
            var p = 1;
            var k = 0;
            while (p < n)
            {
                p *= b;
                k += 1;
            }
            return k;
        }

        int[] _build_header(int m, int k, int pad, int sh)
        {
            /*
            @param m: the total number of shares; 1 <= m <= 256
            @param k: the number of shares required to reconstruct; 1 <= k <= m
            @param pad: the number of bytes of padding added to the file before encoding; 0 <= pad < k
            @param sh: the shnum of this share; 0 <= k < m
            @return: a compressed string encoding m, k, pad, and sh
            */

            var bitsused = 0;
            var val = 0;

            val |= (m - 1);
            bitsused += 8; // the first 8 bits always encode m

            var kbits = log_ceil(m, 2); // num bits needed to store all possible values of k
            val <<= kbits;
            bitsused += kbits;

            val |= (k - 1);

            var padbits = log_ceil(k, 2); // num bits needed to store all possible values of pad
            val <<= padbits;
            bitsused += padbits;

            val |= pad;

            var shnumbits = log_ceil(m, 2); // num bits needed to store all possible values of shnum
            val <<= shnumbits;
            bitsused += shnumbits;

            val |= sh;

            if (bitsused <= 16)
            {
                val <<= (16 - bitsused);
                return new int[] { (val >> 8) & 0xff, (val >> 0) & 0xff };
            }
            if (bitsused <= 24)
            {
                val <<= (24 - bitsused);
                return new int[] { (val >> 16) & 0xff, (val >> 8) & 0xff, (val >> 0) & 0xff };
            }
            val <<= (32 - bitsused);
            return new int[] { (val >> 24) & 0xff, (val >> 16) & 0xff, (val >> 8) & 0xff, (val >> 0) & 0xff };
        }
        int MASK(int bits)
        {
            return (1 << bits) - 1;
        }

        int[] _parse_header(byte[] byte_array)
        {
            /*
            @param inf: an object which I can call read(1) on to get another byte
            @return: tuple of (m, k, pad, sh,); side-effect: the first one to four
                bytes of inf will be read
            */
            // The first 8 bits always encode m.


            var idx = 2;
            var ch = byte_array[0];
            if (ch == 0)
            {
                throw new Exception("Share files corrupted");
            }
            var m = ch + 1;

            // The next few bits encode k.
            var kbits = log_ceil(m, 2); // num bits needed to store all possible values of k
            var b2_bits_left = 8 - kbits;
            var kbitmask = MASK(kbits) << b2_bits_left;
            ch = byte_array[1];
            var k = ((ch & kbitmask) >> b2_bits_left) + 1;

            var shbits = log_ceil(m, 2); // num bits needed to store all possible values of shnum
            var padbits = log_ceil(k, 2); // num bits needed to store all possible values of pad

            var val = ch & (~kbitmask);

            var needed_padbits = padbits - b2_bits_left;
            if (needed_padbits > 0)
            {
                ch = byte_array[idx++];
                val <<= 8;
                val |= ch;
                needed_padbits -= 8;
            }
            //assert needed_padbits <= 0
            var extrabits = -needed_padbits;
            var pad = val >> extrabits;
            val &= MASK(extrabits);

            var needed_shbits = shbits - extrabits;
            if (needed_shbits > 0)
            {
                ch = byte_array[idx++];
                val <<= 8;
                val |= ch;
                needed_shbits -= 8;
            }
            //assert needed_shbits <= 0

            var gotshbits = -needed_shbits;

            var sh = val >> gotshbits;

            return new int[] { m, k, pad, sh, idx };
        }

        byte[] gf_exp = new byte[510];  /* index->poly form conversion table    */
        byte[] gf_log = new byte[(256)]; /* Poly->index form conversion table    */
        byte[] inverse = new byte[(256)]; /* inverse of field elem.               */

        /*
         * modnn(x) computes x % GF_SIZE, where GF_SIZE is 2**GF_BITS - 1,
         * without a slow divide.
         */
        int modnn(int x)
        {
            while (x >= 255)
            {
                x -= 255;
                x = (x >> 8) + (x & 255);
            }
            return x;
        }

        byte[] gf_mul_table = new byte[(256 * 256)];

        /*
         * Generate GF(2**m) from the irreducible polynomial p(X) in p[0]..p[m]
         * Lookup tables:
         *     index->polynomial form		gf_exp[] contains j= \alpha^i;
         *     polynomial form -> index form	gf_log[ j = \alpha^i ] = i
         * \alpha=x is the primitive element of GF(2^m)
         *
         * For efficiency, gf_exp[] has size 2*GF_SIZE, so that a simple
         * multiplication of two numbers can be resolved without calling modnn
         */

        void _init_mul_table()
        {
            int i, j;
            for (i = 0; i < 256; i++)
                for (j = 0; j < 256; j++)
                    gf_mul_table[i * 256 + j] = gf_exp[modnn(gf_log[i] + gf_log[j])];

            for (j = 0; j < 256; j++)
                gf_mul_table[0 * 256 + j] = gf_mul_table[j * 256 + 0] = 0;
        }


        byte gf_mul(byte a, byte b)
        {
            return gf_mul_table[a * 256 + b];
        }

        /*
         * Primitive polynomials - see Lin & Costello, Appendix A,
         * and  Lee & Messerschmitt, p. 453.
         */
        string Pp = "101110001";

        void generate_gf()
        {
            int i = 0;
            byte mask = 0;

            mask = 1;                     /* x ** 0 = 1 */
            gf_exp[8] = 0;          /* will be updated at the end of the 1st loop */
            /*
             * first, generate the (polynomial representation of) powers of \alpha,
             * which are stored in gf_exp[i] = \alpha ** i .
             * At the same time build gf_log[gf_exp[i]] = i .
             * The first 8 powers are simply bits shifted to the left.
             */
            for (i = 0; i < 8; i++, mask <<= 1)
            {
                gf_exp[i] = mask;
                gf_log[gf_exp[i]] = (byte)i;
                /*
                 * If Pp[i] == 1 then \alpha ** i occurs in poly-repr
                 * gf_exp[8] = \alpha ** 8
                 */
                if (Pp[i] == '1')
                    gf_exp[8] ^= mask;
            }
            /*
             * now gf_exp[8] = \alpha ** 8 is complete, so can also
             * compute its inverse.
             */
            gf_log[gf_exp[8]] = 8;
            /*
             * Poly-repr of \alpha ** (i+1) is given by poly-repr of
             * \alpha ** i shifted left one-bit and accounting for any
             * \alpha ** 8 term that may occur when poly-repr of
             * \alpha ** i is shifted.
             */
            mask = 1 << 7;
            for (i = 9; i < 255; i++)
            {
                if (gf_exp[i - 1] >= mask)
                    gf_exp[i] = (byte)(gf_exp[8] ^ ((gf_exp[i - 1] ^ mask) << 1));
                else
                    gf_exp[i] = (byte)(gf_exp[i - 1] << 1);
                gf_log[gf_exp[i]] = (byte)i;
            }
            /*
             * log(0) is not defined, so use a special value
             */
            gf_log[0] = 255;
            /* set the extended gf_exp values for fast multiply */
            for (i = 0; i < 255; i++)
                gf_exp[i + 255] = gf_exp[i];

            /*
             * again special cases. 0 has no inverse. This used to
             * be initialized to 255, but it should make no difference
             * since noone is supposed to read from here.
             */
            inverse[0] = 0;
            inverse[1] = 1;
            for (i = 2; i <= 255; i++)
                inverse[i] = gf_exp[255 - gf_log[i]];
        }


        /*
         * Various linear algebra operations that i use often.
         */

        /*
         * addmul() computes dst[] = dst[] + c * src[]
         * This is used often, so better optimize it! Currently the loop is
         * unrolled 16 times, a good value for 486 and pentium-class machines.
         * The case c=0 is also optimized, whereas c=1 is not. These
         * calls are unfrequent in my typical apps so I did not bother.
         */

        void addmul(byte[] dst, int dst_idx, byte[] src, int src_idx, byte c, int sz)
        {
            int i;
            if (c != 0)
            {
                for (i = 0; i < sz; i++)
                {
                    dst[dst_idx + i] ^= gf_mul(src[src_idx + i], c);
                }
            }
        }

        /*
         * computes C = AB where A is n*k, B is k*m, C is n*m
         */

        byte[] _matmul(byte[] a, byte[] b, byte[] c, byte n, byte k, byte m)
        {
            byte row, col, i;

            for (row = 0; row < n; row++)
            {
                for (col = 0; col < m; col++)
                {
                    byte acc = 0;
                    for (i = 0; i < k; i++)
                        acc ^= gf_mul(a[row * k + i], b[col + m * i]);
                    c[row * m + col] = acc;
                }
            }

            return c;
        }

        byte memcmp(byte[] src, int src_idx, byte[] dst, int dst_idx, int size)
        {
            byte i;
            for (i = 0; i < size; i++)
            {
                if (src[src_idx + i] != dst[dst_idx + i])
                {
                    return 1;
                }
            }
            return 0;
        }

        /*
         * _invert_mat() takes a matrix and produces its inverse
         * k is the size of the matrix.
         * (Gauss-Jordan, adapted from Numerical Recipes in C)
         * Return non-zero if singular.
         */

        void _invert_mat(byte[] src, byte k)
        {
            byte c, p;
            byte irow = 0;
            byte icol = 0;
            byte row, col, i, ix;

            var indxc = new byte[k];
            var indxr = new byte[k];
            var ipiv = new byte[k];
            var id_row = new byte[k];

            /*
             * ipiv marks elements already used as pivots.
             */
            for (i = 0; i < k; i++)
                ipiv[i] = 0;

            for (col = 0; col < k; col++)
            {
                int pivot_row;
                var found_piv = 0;
                /*
                 * Zeroing column 'col', look for a non-zero element.
                 * First try on the diagonal, if it fails, look elsewhere.
                 */
                if (ipiv[col] != 1 && src[col * k + col] != 0)
                {
                    irow = col;
                    icol = col;
                    found_piv = 1;
                }
                for (row = 0; row < k; row++)
                {
                    if (found_piv == 1)
                    {
                        break;
                    }
                    if (ipiv[row] != 1)
                    {
                        for (ix = 0; ix < k; ix++)
                        {
                            if (ipiv[ix] == 0)
                            {
                                if (src[row * k + ix] != 0)
                                {
                                    irow = row;
                                    icol = ix;
                                    found_piv = 1;
                                    break;
                                }
                            }
                            else
                            { } //assert (ipiv[ix] <= 1);
                        }
                    }
                }
                //found_piv:
                ipiv[icol] += 1;
                /*
                 * swap rows irow and icol, so afterwards the diagonal
                 * element will be correct. Rarely done, not worth
                 * optimizing.
                 */
                if (irow != icol)
                    for (ix = 0; ix < k; ix++)
                    {
                        var tmp = src[irow * k + ix];
                        src[irow * k + ix] = src[icol * k + ix];
                        tmp = src[icol * k + ix];
                    }
                indxr[col] = irow;
                indxc[col] = icol;
                //pivot_row = &src[icol * k];
                c = src[icol * k + icol];
                //assert (c != 0);
                if (c != 1)
                {                       /* otherwhise this is a NOP */
                    /*
                     * this is done often , but optimizing is not so
                     * fruitful, at least in the obvious ways (unrolling)
                     */
                    c = inverse[c];
                    src[icol * k + icol] = 1;
                    for (ix = 0; ix < k; ix++)
                        src[icol * k + ix] = gf_mul(c, src[icol * k + ix]);
                }
                /*
                 * from all rows, remove multiples of the selected row
                 * to zero the relevant entry (in fact, the entry is not zero
                 * because we know it must be zero).
                 * (Here, if we know that the pivot_row is the identity,
                 * we can optimize the addmul).
                 */
                id_row[icol] = 1;
                if (memcmp(src, icol * k, id_row, 0, k) != 0)
                {
                    for (p = 0, ix = 0; ix < k; ix++, p += k)
                    {
                        if (ix != icol)
                        {
                            c = src[icol + p];
                            src[icol + p] = 0;
                            addmul(src, p, src, icol * k, c, k);
                        }
                    }
                }
                id_row[icol] = 0;
            }                           /* done all columns */
            for (col = k; col > 0; col--)
                if (indxr[col - 1] != indxc[col - 1])
                    for (row = 0; row < k; row++)
                    {
                        var tmp = src[row * k + indxr[col - 1]];
                        src[row * k + indxr[col - 1]] = src[row * k + indxc[col - 1]];
                        src[row * k + indxc[col - 1]] = tmp;
                    }
        }

        /*
         * fast code for inverting a vandermonde matrix.
         *
         * NOTE: It assumes that the matrix is not singular and _IS_ a vandermonde
         * matrix. Only uses the second column of the matrix, containing the p_i's.
         *
         * Algorithm borrowed from "Numerical recipes in C" -- sec.2.8, but largely
         * revised for my purposes.
         * p = coefficients of the matrix (p_i)
         * q = values of the polynomial (known)
         */
        void _invert_vdm(byte [] src,byte k)
        {
            byte i, j, row, col;
            byte[] b, c, p;
            byte t, xx;

            if (k == 1)                   /* degenerate case, matrix must be p^0 = 1 */
                return;
            /*
             * c holds the coefficient of P(x) = Prod (x - p_i), i=0..k-1
             * b holds the coefficient for the matrix inversion
             */
            c = new byte[(k)];
            b = new byte[(k)];

            p = new byte[(k)];

            for (j = 1, i = 0; i < k; i++, j += k)
            {
                c[i] = 0;
                p[i] = src[j];            /* p[i] */
            }
            /*
             * construct coeffs. recursively. We know c[k] = 1 (implicit)
             * and start P_0 = x - p_0, then at each stage multiply by
             * x - p_i generating P_i = x P_{i-1} - p_i P_{i-1}
             * After k steps we are done.
             */
            c[k - 1] = p[0];              /* really -p(0), but x = -x in GF(2^m) */
            for (i = 1; i < k; i++)
            {
                var p_i = p[i];            /* see above comment */
                for (j =(byte)( k - 1 - (i - 1)); j < k - 1; j++)
                    c[j] ^= gf_mul(p_i, c[j + 1]);
                c[k - 1] ^= p_i;
            }

            for (row = 0; row < k; row++)
            {
                /*
                 * synthetic division etc.
                 */
                xx = p[row];
                t = 1;
                b[k - 1] = 1;             /* this is in fact c[k] */
                for (i = (byte)(k - 1); i > 0; i--)
                {
                    b[i - 1] = (byte)(c[i] ^ gf_mul(xx, b[i]));
                    t = (byte)(gf_mul(xx, t) ^ b[i - 1]);
                }
                for (col = 0; col < k; col++)
                    src[col * k + row] = gf_mul(inverse[t], b[col]);
            }
        }

        void init_fec()
        {
            generate_gf();
            _init_mul_table();
        }

        // init_fec();

        List<byte[]> encode(byte [] src, List<byte> block_number_array = null)
        {
            byte i, j;
            int k;
            var sz = (int)Math.Ceiling((double)src.Length / this.k);
            var pad = sz * this.k - src.Length;
            var fecs = new List<byte[]>();
            int header_length = 0;
            if (block_number_array == null)
            {
                block_number_array =new  List<byte>();
                for (i = 0; i < this.n; i++)
                {
                    block_number_array.Add(i);
                }
            }
            for (i = 0; i < block_number_array.Count; i++)
            {
                var header = _build_header(this.n, this.k, pad, i);
                header_length = header.Length;
                fecs.Add(new byte[(sz + header_length)]);
                for (j = 0; j < header_length; j++)
                {
                    fecs[i][j] = (byte)header[j];
                }
            }

            for (k = 0; k < sz; k += this.stride)
            {
                var stride = ((sz - k) < this.stride) ? (sz - k) : this.stride;
                for (i = 0; i < block_number_array.Count; i++)
                {
                    var fecnum = block_number_array[i];
                    var fec = fecs[i];
                    var p = fecnum * this.k;
                    for (j = 0; j < this.k; j++)
                    {
                        Console.WriteLine("fec " + fecnum + " " + k + " " + this.enc_matrix[p + j] + " " + stride);
                        addmul(fec, header_length + k, src, j * stride + k * this.k, this.enc_matrix[p + j], stride);
                    }
                }
            }
            return fecs;
        }

        private byte[] slice(byte[] vs, int v)
        {
            List<byte> result = new List<byte>();
            for (int i = v; i < vs.Length; i++)
            {
                result.Add(vs[i]);
            }

            return result.ToArray();
        }


        byte[] decode(byte[][] input_array, byte[] indices)
        {
            int row;
            int col;
            int idx;
            int m, k, pad = 0, sh;


            var size_per_row = input_array[0].Length;
            var sz = size_per_row * this.k;
            var output = new byte[sz];



            for (row = 0; row < indices.Length; row++)
            {
                if ((indices[row] < this.k) && (indices[row] != row))
                {
                    var tmp = input_array[row];
                    input_array[row] = input_array[indices[row]];
                    input_array[indices[row]] = tmp;
                    var tmpx = indices[row];
                    indices[row] = indices[tmpx];
                    indices[tmpx] = tmpx;
                }
            }
            var decode_matrix = build_decode_matrix(this, indices.ToArray());


            int col_base = 0;
            for (k = 0; k < size_per_row; k += this.stride)
            {
                var stride = (size_per_row - k < this.stride) ? size_per_row - k : this.stride;
                var out_stride = k * this.k;
                for (row = 0; row < this.k; row++)
                {
                    if (indices[row] < this.k)
                    {
                        for (col = 0; col < stride; col++)
                        {
                            output[row * stride + out_stride + col] = input_array[indices[row]][k + col];
                        }
                    }
                    else
                    {
                        for (col = 0; col < this.k; col++)
                        {
                            addmul(output, row * stride + out_stride, input_array[col], k, decode_matrix[row * this.k + col], stride);
                        }
                    }
                }
            }
            if (pad > 0)
            {

            }
            //output = output.subarray(0, sz - pad);
            return output;
        }


        byte[] decode(byte[][] input_array)
        {
            int row;
            int col;
            var indices =new List<byte>();
            int idx;
            int m, k, pad = 0, sh;
            for (idx = 0; idx < input_array.Length; idx++)
            {
                var tuple = _parse_header(input_array[idx]);
             
                m = tuple[0];
                k = tuple[1];
                pad = tuple[2];
                indices.Add((byte)tuple[3]);
                input_array[idx] = slice(input_array[idx], (tuple[4]));
            }
           
            var size_per_row = input_array[0].Length;
            var sz = size_per_row * this.k;
            var output = new byte[sz];

            for (row = 0; row < indices.Count; row++)
            {
                if ((indices[row] < this.k) && (indices[row] != row))
                {
                    var tmp = input_array[row];
                    input_array[row] = input_array[indices[row]];
                    input_array[indices[row]] = tmp;
                    var  tmpx = indices[row];
                    indices[row] = indices[tmpx];
                    indices[tmpx] = tmpx;
                }
            }



            var decode_matrix = build_decode_matrix(this, indices.ToArray());


            int col_base = 0;
            for (k = 0; k < size_per_row; k += this.stride)
            {
                var stride = (size_per_row - k < this.stride) ? size_per_row - k : this.stride;
                var out_stride = k * this.k;
                for (row = 0; row < this.k; row++)
                {
                    if (indices[row] < this.k)
                    {
                        for (col = 0; col < stride; col++)
                        {
                            output[row * stride + out_stride + col] = input_array[indices[row]][k + col];
                        }
                    }
                    else
                    {
                        for (col = 0; col < this.k; col++)
                        {
                            addmul(output, row * stride + out_stride, input_array[col], k, decode_matrix[row * this.k + col], stride);
                        }
                    }
                }
            }
            if (pad > 0)
            {

            }
            //output = output.subarray(0, sz - pad);
            return output;
        }

   


        /**
            * Build decode matrix into some memory space.
            *
            * @param matrix a space allocated for a k by k matrix
            */
        byte[] build_decode_matrix(fec fec, byte[] indices)
        {
            var k = fec.k;
            var matrix = new byte[k * k];
            int i, j;
            int p;
            for (i = 0, p = 0; i < k; i++, p += k)
            {
                if (indices[i] < k)
                {
                    for (j = 0; j < k; j++)
                    {
                        matrix[p + j] = 0;
                    }
                    matrix[p + indices[i]] = 1;
                }
                else
                {
                    for (j = 0; j < k; j++)
                    {
                        matrix[p + j] = fec.enc_matrix[indices[i] * k + j];
                    }
                }
            }
            _invert_mat(matrix, k);
            return matrix;
        }

        byte[] enc_matrix = null;
        byte k = 0;
        byte n = 0;
       
        int stride = 1024;

        public fec(byte k, byte n)
        {
            init_fec();
            int row, col;
            int p;
            byte[] tmp_m = null;
            this.k = k;
            this.n = n;
            enc_matrix = new byte[n * k];
            tmp_m = new byte[n * k];
            /*
             * fill the matrix with powers of field elements, starting from 0.
             * The first row is special, cannot be computed with exp. table.
             */
            tmp_m[0] = 1;
            for (col = 1; col < k; col++)
                tmp_m[col] = 0;
            for (p = k, row = 0; row < n - 1; row++, p += k)
                for (col = 0; col < k; col++)
                    tmp_m[p + col] = gf_exp[modnn(row * col)];

            /*
             * quick code to build systematic matrix: invert the top
             * k*k vandermonde matrix, multiply right the bottom n-k rows
             * by the inverse, and construct the identity matrix at the top.
             */
            _invert_vdm(tmp_m, k);        /* much faster than _invert_mat */
            var x =_matmul(tmp_m.subarray(k * k), tmp_m, enc_matrix.subarray(k * k, n * k), (byte)(n - k), k, k);

            Array.Copy(x, 0, enc_matrix, k * k, x.Length);
            
            /*
             * the upper matrix is I so do not bother with a slow multiply
             */
            int i;
            for (i = 0; i < k * k; i++)
            {
                enc_matrix[i] = 0;
            }
            for (p = 0, col = 0; col < k; col++, p += k + 1)
            {
                enc_matrix[p] = 1;
            }

          
        }


 

        static void Main()
        {
            var valuea = "1 2 3 4 5 6 7 8 9 10".Split(' ').Select(r => byte.Parse(r)).ToArray();
            var valueb = "11 12 13 14 15 16 17 18 19 20".Split(' ').Select(r => byte.Parse(r)).ToArray();
            var valuec = "21 30 31 16 17 42 43 60 61 54".Split(' ').Select(r => byte.Parse(r)).ToArray();
            List<byte[]> input = new List<byte[]>();
            input.Add(valuea);
            //input.Add(valueb);
            input.Add(valuec);
            var result = new fec(2, 3).decode(input.ToArray(), new byte[] { 0, 2 });
            input = new List<byte[]>();
            //input.Add(valuea);
            input.Add(valueb);
            input.Add(valuec);
            result = new fec(2, 3).decode(input.ToArray(), new byte[] { 1, 2 });

            var bytesx = new byte[20];
            for (int i = 0; i < 10; i++)
            {
                bytesx[i] = (byte)(i + 1);
            }
            for (int i = 0; i < 10; i++)
            {
                bytesx[10 + i] = (byte)(i + 11);
            }
            var code = new fec(2, 3).encode(bytesx);
            code.RemoveAt(0);
            var bytes = new fec(2, 3).decode(code.ToArray());

            var subcode = new List<byte[]>();
            subcode.Add(code[1]);
            subcode.Add(code[2]);
            bytes = new fec(2, 3).decode(subcode.ToArray());

            var test = new byte[1024];
            for (int i = 0; i < test.Length; i++)
            {
                test[i] = (byte)(i % 255);
            }
            code = new fec(2, 3).encode(test);
            for (int i = 0; i < 10; i++)
            {
                code[0][new Random(Guid.NewGuid().GetHashCode()).Next(0, 500)] = 1;
                code[2][new Random(Guid.NewGuid().GetHashCode()).Next(0, 500)] = 2;
                
            }
            code.RemoveAt(0);

            var xbytes = new fec(2, 3).decode(code.ToArray());

            int count = 0;
            for (int i = 0; i < xbytes.Length; i++)
            {
                if (xbytes[i] != test[i])
                {
                    count++;
                }
            }
            Console.WriteLine("Error Count:" + count);
            Console.WriteLine("" + System.Text.Encoding.ASCII.GetString(bytes));

        }
    }

    public static class Exction
    {
        public static byte[] subarray(this byte[] buff, int index,int count = -1)
        {
            if (count <= -1)
            {
                count = buff.Length - index;
            }
            byte[] result = new byte[buff.Length - index];
            Array.Copy(buff, index, result, 0, result.Length);
            return result;
        }
    }
}