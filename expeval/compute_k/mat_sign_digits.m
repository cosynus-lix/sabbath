function Y = mat_sign_digits(X,num_digits)
%SIGN_DIGITS Summary of this function goes here
%   Detailed explanation goes here
[a,b] = size(X);
Y = zeros(a,b);
for ind1=1:a
    for ind2=1:b
        L=sign_digits(X(ind1,ind2), num_digits);
        Y(ind1,ind2) = L ;
    end
end

end

