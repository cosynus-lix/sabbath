function x_prime = differential_homo_complete(t, x, size_str)
%DIFFERENTIAL_HOMO_COMPLETE Summary of this function goes here
%   Detailed explanation goes here
load("First_try_piecewise_Lyap_size_"+size_str+".mat")

if invar_mode0_ge * x >= 0
    x_prime = A_0_homo_complete * x;
else
    x_prime = A_1_homo_complete * x;
end
end

