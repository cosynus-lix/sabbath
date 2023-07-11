function y = sign_digits(x,num_digits)
%SIGN_DIGITS Summary of this function goes here
%   Detailed explanation goes here
if abs(x) < 3*10^(-16)
    y=0;
else
bla = 0;
if x < 0
    x = -x;
    bla = 1;
end
expon = floor (log10(x) );
y = floor(x / 10^(expon - (num_digits-1))) * 10^(expon - (num_digits-1));
if bla == 1
    y = -y;
end
end
end

